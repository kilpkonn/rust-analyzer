use hir::{
    db::{ExpandDatabase, HirDatabase},
    Adt, AssocItem, ClosureStyle, Const, ConstParam, Function, GenericParam, HirDisplay, Impl,
    Local, Module, ModuleDef, ScopeDef, Static, Struct, StructKind, Type, Variant,
};
use ide_db::{
    assists::{Assist, AssistId, AssistKind, GroupLabel},
    label::Label,
    source_change::SourceChange,
    FxHashSet,
};
use text_edit::TextEdit;

use crate::{Diagnostic, DiagnosticCode, DiagnosticsContext};

use std::iter::{self, Extend};

use itertools::Itertools;

use syntax::AstNode;

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
            ScopeDef::ModuleDef(ModuleDef::Module(_it)) => {
                // it.declarations(db)
                //     .into_iter()
                //     .for_each(|def| process_def(ScopeDef::ModuleDef(def), funcs, vars, db));
            }
            ScopeDef::GenericParam(GenericParam::ConstParam(it)) => {
                vars.push(TypeInhabitant::ConstParam(it));
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

    vars = vars.into_iter().unique().collect();
    funcs = funcs.into_iter().unique().collect();

    // dbg!(&names);
    let mut paths = dfs_term_search(&d.expected, &vars, &funcs, db, 2);
    paths.sort_by(|(d1, _), (d2, _)| d1.cmp(d2));

    let mut assists = vec![];
    for (_d, path) in paths {
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
    }
    dbg!(&assists.iter().map(|a| a.label.to_string()).collect::<Vec<_>>());
    if !assists.is_empty() {
        Some(assists)
    } else {
        None
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
enum TypeInhabitant {
    Const(Const),
    Static(Static),
    Local(Local),
    ConstParam(ConstParam),
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
            TypeInhabitant::ConstParam(it) => (it.name(db), it.module(db)),
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
            TypeInhabitant::ConstParam(it) => it.ty(db),
        }
    }
    fn could_unify_with_normalized(&self, db: &dyn HirDatabase, ty: &Type) -> bool {
        self.ty(db).could_unify_with_normalized(db, ty)
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
enum TypeTransformation {
    Function(Function),
    ImplFunction(Function, Impl),
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
    fn could_unify_with_normalized(&self, db: &dyn HirDatabase, ty: &Type) -> bool {
        self.ret_ty(db).could_unify_with_normalized(db, ty)
    }

    fn ret_ty(&self, db: &dyn HirDatabase) -> Type {
        match self {
            Self::Function(it) => it.ret_type(db),
            Self::ImplFunction(it, imp) => it.ret_type_for_impl(&imp, db),
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
                let args = params.iter().map(|f| f.gen_source_code(items_in_scope, ctx)).join(", ");
                let sig = format!("{}({})", it.name(db).display(db).to_string(), args);
                format!("{}{}", gen_module_prefix(it.module(db), items_in_scope, db), sig)
            }
            Self::ImplFunction(it, _imp) => {
                let target =
                    params.first().expect("no self param").gen_source_code(items_in_scope, ctx);
                let args = params
                    .iter()
                    .skip(1)
                    .map(|f| f.gen_source_code(items_in_scope, ctx))
                    .join(", ");
                format!("{}.{}({})", target, it.name(db).display(db).to_string(), args)
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

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
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

    fn ty(&self, db: &dyn HirDatabase) -> Type {
        match self {
            TypeTree::TypeInhabitant(it) => it.ty(db),
            TypeTree::TypeTransformation { func, .. } => func.ret_ty(db),
        }
    }

    fn could_unify_with_normalized(&self, db: &dyn HirDatabase, ty: &Type) -> bool {
        self.ty(db).could_unify_with_normalized(db, ty)
    }
}

fn dfs_search_assoc_item(
    tt: &TypeTree,
    vars: &[TypeInhabitant],
    funcs: &[TypeTransformation],
    db: &dyn HirDatabase,
    depth: u32,
) -> Vec<(u32, TypeTree)> {
    if depth == 0 {
        return Vec::new();
    }

    Impl::all_for_type(db, tt.ty(db))
        .into_iter()
        .flat_map(|imp| {
            imp.items(db)
                .into_iter()
                .filter_map(|it| match it {
                    AssocItem::Function(f) => Some(f),
                    _ => None,
                })
                .flat_map(move |func| {
                    let param_trees: Vec<Vec<(u32, TypeTree)>> =
                        iter::once(vec![(depth, tt.clone())])
                            .chain(func.params_without_self(db).into_iter().map(|param| {
                                let tts = dfs_term_search(
                                    param.ty(),
                                    vars,
                                    funcs,
                                    db,
                                    depth.saturating_sub(1),
                                );
                                let max = tts.iter().map(|(d, _)| *d).max().unwrap_or(0);
                                tts.into_iter().filter(|(d, _)| *d >= max).collect()
                            }))
                            .collect();

                    let mut new_tts: Vec<(u32, TypeTree)> = param_trees
                        .into_iter()
                        .multi_cartesian_product()
                        .map(|params| {
                            (
                                params.iter().map(|(d, _)| *d).min().unwrap_or(0),
                                TypeTree::TypeTransformation {
                                    func: TypeTransformation::ImplFunction(func, imp),
                                    params: params.into_iter().map(|(_, p)| p).collect(),
                                },
                            )
                        })
                        .collect();

                    let rec_res: Vec<(u32, TypeTree)> = new_tts
                        .iter()
                        .flat_map(|(d, new_tt)| {
                            dfs_search_assoc_item(&new_tt, vars, funcs, db, d.saturating_sub(1))
                                .into_iter()
                        })
                        .collect();

                    new_tts.extend(rec_res);
                    Some(new_tts)
                })
        })
        .flatten()
        .unique()
        .collect()
}

fn dfs_term_search(
    goal: &Type,
    vars: &[TypeInhabitant],
    funcs: &[TypeTransformation],
    db: &dyn HirDatabase,
    depth: u32,
) -> Vec<(u32, TypeTree)> {
    if depth == 0 {
        return Vec::new();
    }

    let mut fulfilling_vars: Vec<(u32, TypeTree)> = vars
        .iter()
        .filter(|&ty| ty.could_unify_with_normalized(db, goal))
        .map(|it| (depth, TypeTree::TypeInhabitant(it.clone())))
        .collect();

    let forward_pass_types: Vec<(u32, TypeTree)> = vars
        .iter()
        .filter(|it| match it {
            TypeInhabitant::Local(_) => true,
            _ => false,
        })
        .flat_map(|tt| {
            dfs_search_assoc_item(
                &TypeTree::TypeInhabitant(tt.clone()),
                vars,
                funcs,
                db,
                depth.saturating_sub(1),
            )
        })
        .filter(|(_, tt)| tt.could_unify_with_normalized(db, goal))
        .collect();

    fulfilling_vars.extend(forward_pass_types);

    let backward_pass: Vec<(u32, TypeTree)> = funcs
        .iter()
        .filter(|tr| tr.could_unify_with_normalized(db, goal))
        .filter_map(|tr| match tr {
            TypeTransformation::Function(func) => {
                let mut param_trees = func.assoc_fn_params(db).into_iter().map(|param| {
                    dfs_term_search(param.ty(), vars, funcs, db, depth.saturating_sub(1))
                });
                build_permutations(&mut param_trees, tr.clone())
            }
            TypeTransformation::ImplFunction(_, _) => None,
            TypeTransformation::Variant(variant) => {
                let mut param_trees = variant.fields(db).into_iter().map(|field| {
                    dfs_term_search(&field.ty(db), vars, funcs, db, depth.saturating_sub(1))
                });
                build_permutations(&mut param_trees, tr.clone())
            }
            TypeTransformation::Struct(strukt) => {
                let mut param_trees = strukt.fields(db).into_iter().map(|field| {
                    dfs_term_search(&field.ty(db), vars, funcs, db, depth.saturating_sub(1))
                });
                build_permutations(&mut param_trees, tr.clone())
            }
        })
        .flatten()
        .collect();
    fulfilling_vars.extend(backward_pass);

    fulfilling_vars.into_iter().unique().collect()
}

fn build_permutations<'a>(
    param_trees: &'a mut dyn Iterator<Item = Vec<(u32, TypeTree)>>,
    tt: TypeTransformation,
) -> Option<Vec<(u32, TypeTree)>> {
    // Extra case for transformations with 0 params
    let (param_trees, count_tree) = param_trees.tee();
    if count_tree.count() == 0 {
        return Some(vec![(
            0,
            TypeTree::TypeTransformation { func: tt.clone(), params: Vec::new() },
        )]);
    }
    let res: Vec<_> = param_trees
        .multi_cartesian_product()
        .map(move |params| {
            (
                params.iter().map(|(d, _)| *d).min().unwrap_or(0),
                TypeTree::TypeTransformation {
                    func: tt.clone(),
                    params: params.into_iter().map(|(_, p)| p).collect(),
                },
            )
        })
        .collect();

    Some(res)
}

#[cfg(test)]
mod tests {
    use crate::tests::{check_diagnostics, check_fixes_unordered, check_has_fix};

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
        check_fixes_unordered(
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
    let _: Foo = C;
               //^ error: invalid `_` expression, expected type `fn()`
}
"#,
            ],
        );
    }

    #[test]
    fn local_item_use_trait() {
        check_has_fix(
            r#"
struct Bar;
trait Foo {
    fn foo(self) -> Bar;
}
impl Foo for i32 {
    fn foo(self) -> Bar {
        unimplemented!()
    }
}
fn asd() -> Bar {
    let a: i32 = 1;
    _$0
}
"#,
            r"
struct Bar;
trait Foo {
    fn foo(self) -> Bar;
}
impl Foo for i32 {
    fn foo(self) -> Bar {
        unimplemented!()
    }
}
fn asd() -> Bar {
    let a: i32 = 1;
    a.foo()
}
",
        );
    }

    #[test]
    fn init_struct() {
        check_has_fix(
            r#"struct Abc {}
struct Qwe { a: i32, b: Abc }
fn main() {
    let a: i32 = 1;
    let c: Qwe = _$0;
}"#,
            r#"struct Abc {}
struct Qwe { a: i32, b: Abc }
fn main() {
    let a: i32 = 1;
    let c: Qwe = Qwe { a: a, b: Abc {  } };
}"#,
        );
    }

    #[test]
    fn ignore_impl_func_with_incorrect_return() {
        check_has_fix(
            r#"
struct Bar {}
trait Foo {
    type Res;
    fn foo(&self) -> Self::Res;
}
impl Foo for i32 {
    type Res = Self;
    fn foo(&self) -> Self::Res { 1 }
}
fn main() {
    let a: i32 = 1;
    let c: Bar = _$0;
}"#,
            r#"
struct Bar {}
trait Foo {
    type Res;
    fn foo(&self) -> Self::Res;
}
impl Foo for i32 {
    type Res = Self;
    fn foo(&self) -> Self::Res { 1 }
}
fn main() {
    let a: i32 = 1;
    let c: Bar = Bar {  };
}"#,
        );
    }

    #[test]
    fn use_impl_func_with_correct_return() {
        check_has_fix(
            r#"
struct Bar {}
trait Foo {
    type Res;
    fn foo(&self) -> Self::Res;
}
impl Foo for i32 {
    type Res = Bar;
    fn foo(&self) -> Self::Res { Bar { } }
}
fn main() {
    let a: i32 = 1;
    let c: Bar = _$0;
}"#,
            r#"
struct Bar {}
trait Foo {
    type Res;
    fn foo(&self) -> Self::Res;
}
impl Foo for i32 {
    type Res = Bar;
    fn foo(&self) -> Self::Res { Bar { } }
}
fn main() {
    let a: i32 = 1;
    let c: Bar = a.foo();
}"#,
        );
    }
}
