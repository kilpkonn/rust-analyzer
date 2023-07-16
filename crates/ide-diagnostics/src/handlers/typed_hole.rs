use hir::{db::ExpandDatabase, ClosureStyle, HirDisplay, StructKind};
use ide_db::{
    assists::{Assist, AssistId, AssistKind, GroupLabel},
    label::Label,
    source_change::SourceChange,
};
use text_edit::TextEdit;

use crate::{Diagnostic, DiagnosticCode, DiagnosticsContext};

use std::iter::{self, Extend};

use hir::{db::HirDatabase, Adt, Const, Function, Local, ModuleDef, Static, Struct, Type, Variant};
use hir::{AssocItem, Impl, Module, ScopeDef};
use ide_db::FxHashSet;
use itertools::Itertools;

use syntax::{ast, AstNode};

// Diagnostic: typed-hole
//
// This diagnostic is triggered when an underscore expression is used in an invalid position.
pub(crate) fn typed_hole(ctx: &DiagnosticsContext<'_>, d: &hir::TypedHole) -> Diagnostic {
    let display_range = ctx.sema.diagnostics_display_range(d.expr.clone().map(|it| it.into()));
    let (message, fixes) = if d.expected.is_unknown() {
        ("`_` expressions may only appear on the left-hand side of an assignment".to_owned(), None)
    } else {
        (
            format!(
                "invalid `_` expression, expected type `{}`",
                d.expected.display(ctx.sema.db).with_closure_style(ClosureStyle::ClosureWithId),
            ),
            fixes(ctx, d),
        )
    };

    Diagnostic::new(DiagnosticCode::RustcHardError("typed-hole"), message, display_range.range)
        .with_fixes(fixes)
}

fn fixes(ctx: &DiagnosticsContext<'_>, d: &hir::TypedHole) -> Option<Vec<Assist>> {
    let db = ctx.sema.db;
    let root = db.parse_or_expand(d.expr.file_id);
    let original_range =
        d.expr.as_ref().map(|it| it.to_node(&root)).syntax().original_file_range_opt(db)?;
    let scope = ctx.sema.scope(d.expr.value.to_node(&root).syntax())?;
    let mut assists = vec![];

    let scope = ctx.sema.scope(d.expr.value.to_node(&root).syntax())?;
    dbg!(&scope);

    let mut funcs = Vec::default();
    let mut vars = Vec::default();
    let mut names = Vec::default();
    let mut items_in_scope = FxHashSet::default();
    items_in_scope.insert(ScopeDef::ModuleDef(ModuleDef::Module(scope.module())));

    fn process_def(
        def: ScopeDef,
        funcs: &mut Vec<TypeTransformation>,
        vars: &mut Vec<TypeInhabitant>,
        db: &dyn HirDatabase,
    ) {
        match def {
            ScopeDef::ModuleDef(ModuleDef::Function(it)) => {
                funcs.push(TypeTransformation::Function(it));
            }
            ScopeDef::ModuleDef(ModuleDef::Const(it)) => {
                vars.push(TypeInhabitant::Const(it));
            }
            ScopeDef::ModuleDef(ModuleDef::Static(it)) => {
                vars.push(TypeInhabitant::Static(it));
            }
            ScopeDef::ModuleDef(ModuleDef::Variant(it)) => {
                funcs.push(TypeTransformation::Variant(it));
            }
            ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Enum(it))) => {
                let variants = it.variants(db).into_iter().map(|v| TypeTransformation::Variant(v));
                funcs.extend(variants);
            }
            ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Struct(it))) => {
                funcs.push(TypeTransformation::Struct(it));
            }
            ScopeDef::ModuleDef(ModuleDef::Module(it)) => {
                // it.declarations(db)
                //     .into_iter()
                //     .for_each(|def| process_def(ScopeDef::ModuleDef(def), funcs, vars, db));
            }
            ScopeDef::Local(it) => {
                vars.push(TypeInhabitant::Local(it));
            }
            _ => {}
        };
    }
    scope.process_all_names(&mut |name, def| {
        names.push(format!("{} - {:?}", name.display(db).to_string(), def));
        items_in_scope.insert(def);
        process_def(def, &mut funcs, &mut vars, db);
    });

    dbg!(names);

    let path = dfs_term_search(&d.expected, &vars, &funcs, db, 3, ctx)?;
    let code = path.gen_source_code(&items_in_scope, ctx);

    assists.push(Assist {
        id: AssistId("typed-hole", AssistKind::QuickFix),
        label: Label::new(format!("Replace `_` with `{}`", &code)),
        group: Some(GroupLabel("Replace `_` with a term".to_owned())),
        target: original_range.range,
        source_change: Some(SourceChange::from_text_edit(
            original_range.file_id,
            TextEdit::replace(original_range.range, code),
        )),
        trigger_signature_help: false,
    });
    if assists.is_empty() {
        None
    } else {
        Some(assists)
    }
}

#[derive(Clone, Eq, Hash, PartialEq)]
enum TypeInhabitant {
    Const(Const),
    Static(Static),
    Local(Local),
}

impl TypeInhabitant {
    fn gen_source_code(
        &self,
        items_in_scope: &FxHashSet<ScopeDef>,
        ctx: &DiagnosticsContext<'_>,
    ) -> String {
        let db = ctx.sema.db;
        let (name, module) = match self {
            TypeInhabitant::Const(it) => (it.name(db).expect("Sum Ting Wong!?!"), it.module(db)),
            TypeInhabitant::Static(it) => (it.name(db), it.module(db)),
            TypeInhabitant::Local(it) => (it.name(db), it.module(db)),
        };
        let name = name.display(db).to_string();
        let prefix = gen_module_prefix(module, items_in_scope, db);
        format!("{}{}", prefix, name)
    }

    fn ty(&self, db: &dyn HirDatabase) -> Type {
        match self {
            TypeInhabitant::Const(it) => it.ty(db),
            TypeInhabitant::Static(it) => it.ty(db),
            TypeInhabitant::Local(it) => it.ty(db),
        }
    }
    fn could_unify_with(&self, db: &dyn HirDatabase, ty: &Type) -> bool {
        let self_ty = match self {
            Self::Const(it) => it.ty(db),
            Self::Static(it) => it.ty(db),
            Self::Local(it) => it.ty(db),
        };
        self_ty.could_unify_with(db, ty)
    }
}

#[derive(Clone, Eq, Hash, PartialEq)]
enum TypeTransformation {
    Function(Function),
    Variant(Variant),
    Struct(Struct),
}

fn gen_module_prefix(
    mut module: Module,
    items_in_scope: &FxHashSet<ScopeDef>,
    db: &dyn HirDatabase,
) -> String {
    let mut prefix = String::new();
    while !items_in_scope.contains(&ScopeDef::ModuleDef(ModuleDef::Module(module))) {
        let mod_name = match module.name(db) {
            Some(m) => m.display(db.upcast()).to_string(),
            None => String::from("<no_mod_name>"),
        };
        prefix = format!("{}::{}", mod_name, prefix);
        match module.parent(db) {
            Some(m) => module = m,
            None => break,
        };
    }
    prefix
}

impl TypeTransformation {
    fn could_unify_with(&self, db: &dyn HirDatabase, ty: &Type) -> bool {
        match self {
            Self::Function(it) => it.ret_type(db).could_unify_with(db, ty),
            Self::Variant(it) => it.parent_enum(db).ty(db).could_unify_with(db, ty),
            Self::Struct(it) => it.ty(db).could_unify_with(db, ty),
        }
    }

    fn ret_ty(&self, db: &dyn HirDatabase) -> Type {
        match self {
            Self::Function(it) => it.ret_type(db),
            Self::Variant(it) => it.parent_enum(db).ty(db),
            Self::Struct(it) => it.ty(db),
        }
    }
    fn gen_source_code(
        &self,
        params: &[TypeTree],
        items_in_scope: &FxHashSet<ScopeDef>,
        ctx: &DiagnosticsContext<'_>,
    ) -> String {
        let db = ctx.sema.db;
        match self {
            Self::Function(it) => {
                if it.has_self_param(db) {
                    let target =
                        params.first().expect("asdasd").gen_source_code(items_in_scope, ctx);
                    let args = params
                        .iter()
                        .skip(1)
                        .map(|f| f.gen_source_code(items_in_scope, ctx))
                        .join(", ");
                    format!("{}.{}({})", target, it.name(db).display(db).to_string(), args)
                } else {
                    let args =
                        params.iter().map(|f| f.gen_source_code(items_in_scope, ctx)).join(", ");
                    let sig = format!("{}({})", it.name(db).display(db).to_string(), args);
                    format!("{}{}", gen_module_prefix(it.module(db), items_in_scope, db), sig)
                }
            }
            Self::Variant(variant) => {
                let inner = match variant.kind(db) {
                    StructKind::Tuple => {
                        let args = params
                            .iter()
                            .map(|f| f.gen_source_code(items_in_scope, ctx))
                            .join(", ");
                        format!("{}({})", variant.name(db).display(db).to_string(), args)
                    }
                    StructKind::Record => {
                        let fields = variant.fields(db);
                        let args = params
                            .iter()
                            .zip(fields.iter())
                            .map(|(a, f)| {
                                format!(
                                    "{}: {}",
                                    f.name(db).display(db).to_string(),
                                    a.gen_source_code(items_in_scope, ctx)
                                )
                            })
                            .join(", ");
                        format!("{} {{ {} }}", variant.name(db).display(db).to_string(), args)
                    }
                    StructKind::Unit => variant.name(db).display(db).to_string(),
                };
                if items_in_scope.contains(&ScopeDef::ModuleDef(ModuleDef::Variant(*variant))) {
                    inner
                } else {
                    let sig = format!(
                        "{}::{}",
                        variant.parent_enum(db).name(db).display(db).to_string(),
                        inner,
                    );
                    format!("{}{}", gen_module_prefix(variant.module(db), items_in_scope, db), sig)
                }
            }
            Self::Struct(it) => {
                let fields = it.fields(db);
                let args = params
                    .iter()
                    .zip(fields.iter())
                    .map(|(a, f)| {
                        format!(
                            "{}: {}",
                            f.name(db).display(db).to_string(),
                            a.gen_source_code(items_in_scope, ctx)
                        )
                    })
                    .join(", ");
                let sig = format!("{} {{ {} }}", it.name(db).display(db).to_string(), args);
                format!("{}{}", gen_module_prefix(it.module(db), items_in_scope, db), sig)
            }
        }
    }
}

#[derive(Clone)]
enum TypeTree {
    /// Leaf node
    TypeInhabitant(TypeInhabitant),
    /// Node with children
    TypeTransformation { func: TypeTransformation, params: Vec<TypeTree> },
}

impl TypeTree {
    fn gen_source_code(
        &self,
        items_in_scope: &FxHashSet<ScopeDef>,
        ctx: &DiagnosticsContext<'_>,
    ) -> String {
        match self {
            TypeTree::TypeInhabitant(it) => it.gen_source_code(items_in_scope, ctx),
            TypeTree::TypeTransformation { func, params } => {
                func.gen_source_code(&params, items_in_scope, ctx)
            }
        }
    }

    fn find_typetree_for_type(&self, ty: &Type, db: &dyn HirDatabase) -> Option<&TypeTree> {
        match self {
            TypeTree::TypeInhabitant(it) => {
                if it.ty(db).could_unify_with(db, ty) {
                    Some(self)
                } else {
                    None
                }
            }
            TypeTree::TypeTransformation { func, params } => {
                if func.could_unify_with(db, ty) {
                    Some(self)
                } else {
                    params.iter().find(|it| it.ty(db).could_unify_with(db, ty))
                }
            }
        }
    }

    fn ty(&self, db: &dyn HirDatabase) -> Type {
        match self {
            TypeTree::TypeInhabitant(it) => it.ty(db),
            TypeTree::TypeTransformation { func, .. } => func.ret_ty(db),
        }
    }
}

fn dfs_search_assoc_item(
    tt: &TypeTree,
    assoc_item: AssocItem,
    vars: &[TypeInhabitant],
    funcs: &[TypeTransformation],
    db: &dyn HirDatabase,
    depth: u32,
    a: &DiagnosticsContext<'_>,
) -> Vec<TypeTree> {
    if depth == 0 {
        return Vec::new();
    }

    let item = match assoc_item {
        AssocItem::Function(it) => it,
        AssocItem::Const(_) => return Vec::new(),
        AssocItem::TypeAlias(_) => return Vec::new(),
    };

    let ret_ty = item.ret_type(db);
    if tt.ty(db).could_unify_with(db, &item.ret_type(db)) {
        return Vec::new();
    }

    // let dbg = assoc_item.name(db).unwrap().display(db.upcast()).to_string();

    let params =
        match item.params_without_self(db).into_iter().fold(Some(Vec::new()), |acc, param| {
            acc.and_then(|mut params| {
                dfs_term_search(param.ty(), vars, funcs, db, depth.saturating_sub(1), a).and_then(
                    |param| {
                        params.push(param);
                        Some(params)
                    },
                )
            })
        }) {
            Some(mut params) => {
                params.insert(0, tt.clone());
                params
            }
            None => Vec::new(),
        };
    let new_tt = TypeTree::TypeTransformation { func: TypeTransformation::Function(item), params };

    if vars.iter().find(|ty| ty.could_unify_with(db, &ret_ty)).is_some() {
        // let dbg = result.first().unwrap().gen_source_code(&Default::default(), a);
        return vec![new_tt];
    }

    let result = iter::once(new_tt)
        .chain(
            Impl::all_for_type(db, ret_ty)
                .into_iter()
                .flat_map(|imp| imp.items(db).into_iter())
                .flat_map(|it| {
                    dfs_search_assoc_item(tt, it, vars, funcs, db, depth.saturating_sub(1), a)
                }),
        )
        .collect();
    result
}

fn dfs_term_search(
    goal: &Type,
    vars: &[TypeInhabitant],
    funcs: &[TypeTransformation],
    db: &dyn HirDatabase,
    depth: u32,
    a: &DiagnosticsContext<'_>,
) -> Option<TypeTree> {
    if depth == 0 {
        return None;
    }

    if let Some(ty) = vars.iter().find(|&ty| ty.could_unify_with(db, goal)) {
        return Some(TypeTree::TypeInhabitant(ty.clone()));
    };

    let forward_pass_types: Vec<TypeTree> = vars
        .iter()
        .filter(|it| match it {
            TypeInhabitant::Local(_) => true,
            _ => false,
        })
        .flat_map(|tt| {
            Impl::all_for_type(db, tt.ty(db)).into_iter().flat_map(|imp| {
                imp.items(db).into_iter().flat_map(|it| {
                    dfs_search_assoc_item(
                        &TypeTree::TypeInhabitant(tt.clone()),
                        it,
                        vars,
                        funcs,
                        db,
                        depth.saturating_sub(1),
                        a,
                    )
                })
            })
        })
        .collect();

    let dbg: Vec<_> =
        forward_pass_types.iter().map(|t| t.gen_source_code(&Default::default(), a)).collect();

    if let Some(tt) = forward_pass_types.iter().find(|it| it.ty(db).could_unify_with(db, goal)) {
        return Some(tt.clone());
    }

    let func =
        funcs.iter().filter(|func| func.could_unify_with(db, goal)).find_map(|tt| match tt {
            TypeTransformation::Function(func) => {
                let params: Vec<TypeTree> =
                    func.assoc_fn_params(db).into_iter().fold(Some(Vec::new()), |acc, param| {
                        acc.and_then(|mut params| {
                            dfs_term_search(param.ty(), vars, funcs, db, depth.saturating_sub(1), a)
                                .and_then(|param| {
                                    params.push(param);
                                    Some(params)
                                })
                        })
                    })?;

                let node = TypeTree::TypeTransformation { func: tt.clone(), params };
                Some(node)
            }
            TypeTransformation::Variant(variant) => {
                let fields: Vec<TypeTree> =
                    variant.fields(db).into_iter().fold(Some(Vec::new()), |acc, field| {
                        acc.and_then(|mut fields| {
                            dfs_term_search(
                                &field.ty(db),
                                vars,
                                funcs,
                                db,
                                depth.saturating_sub(1),
                                a,
                            )
                            .and_then(|field| {
                                fields.push(field);
                                Some(fields)
                            })
                        })
                    })?;
                let node = TypeTree::TypeTransformation { func: tt.clone(), params: fields };
                Some(node)
            }
            TypeTransformation::Struct(strukt) => {
                let fields: Vec<TypeTree> =
                    strukt.fields(db).into_iter().fold(Some(Vec::new()), |acc, field| {
                        acc.and_then(|mut fields| {
                            dfs_term_search(
                                &field.ty(db),
                                vars,
                                funcs,
                                db,
                                depth.saturating_sub(1),
                                a,
                            )
                            .and_then(|field| {
                                fields.push(field);
                                Some(fields)
                            })
                        })
                    })?;

                let node = TypeTree::TypeTransformation { func: tt.clone(), params: fields };
                Some(node)
            }
        });

    if func.is_some() {
        return func;
    }

    None
}

#[cfg(test)]
mod tests {
    use crate::tests::{check_diagnostics, check_fixes};

    #[test]
    fn unknown() {
        check_diagnostics(
            r#"
fn main() {
    _;
  //^ error: `_` expressions may only appear on the left-hand side of an assignment
}
"#,
        );
    }

    #[test]
    fn concrete_expectation() {
        check_diagnostics(
            r#"
fn main() {
    if _ {}
     //^ error: invalid `_` expression, expected type `bool`
    let _: fn() -> i32 = _;
                       //^ error: invalid `_` expression, expected type `fn() -> i32`
    let _: fn() -> () = _; // FIXME: This should trigger an assist because `main` matches via *coercion*
                      //^ error: invalid `_` expression, expected type `fn()`
}
"#,
        );
    }

    #[test]
    fn integer_ty_var() {
        check_diagnostics(
            r#"
fn main() {
    let mut x = 3;
    x = _;
      //^ 💡 error: invalid `_` expression, expected type `i32`
}
"#,
        );
    }

    #[test]
    fn ty_var_resolved() {
        check_diagnostics(
            r#"
fn main() {
    let mut x = t();
    x = _;
      //^ 💡 error: invalid `_` expression, expected type `&str`
    x = "";
}
fn t<T>() -> T { loop {} }
"#,
        );
    }

    #[test]
    fn valid_positions() {
        check_diagnostics(
            r#"
fn main() {
    let x = [(); _];
    let y: [(); 10] = [(); _];
    _ = 0;
    (_,) = (1,);
}
"#,
        );
    }

    #[test]
    fn check_quick_fix() {
        check_fixes(
            r#"
enum Foo {
    Bar
}
use Foo::Bar;
const C: Foo = Foo::Bar;
fn main<const CP: Foo>(param: Foo) {
    let local = Foo::Bar;
    let _: Foo = _$0;
               //^ error: invalid `_` expression, expected type `fn()`
}
"#,
            vec![
                r#"
enum Foo {
    Bar
}
use Foo::Bar;
const C: Foo = Foo::Bar;
fn main<const CP: Foo>(param: Foo) {
    let local = Foo::Bar;
    let _: Foo = local;
               //^ error: invalid `_` expression, expected type `fn()`
}
"#,
                r#"
enum Foo {
    Bar
}
use Foo::Bar;
const C: Foo = Foo::Bar;
fn main<const CP: Foo>(param: Foo) {
    let local = Foo::Bar;
    let _: Foo = param;
               //^ error: invalid `_` expression, expected type `fn()`
}
"#,
                r#"
enum Foo {
    Bar
}
use Foo::Bar;
const C: Foo = Foo::Bar;
fn main<const CP: Foo>(param: Foo) {
    let local = Foo::Bar;
    let _: Foo = CP;
               //^ error: invalid `_` expression, expected type `fn()`
}
"#,
                r#"
enum Foo {
    Bar
}
use Foo::Bar;
const C: Foo = Foo::Bar;
fn main<const CP: Foo>(param: Foo) {
    let local = Foo::Bar;
    let _: Foo = Bar;
               //^ error: invalid `_` expression, expected type `fn()`
}
"#,
                r#"
enum Foo {
    Bar
}
use Foo::Bar;
const C: Foo = Foo::Bar;
fn main<const CP: Foo>(param: Foo) {
    let local = Foo::Bar;
    let _: Foo = C;
               //^ error: invalid `_` expression, expected type `fn()`
}
"#,
            ],
        );
    }
}
