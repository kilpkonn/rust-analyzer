use hir::{
    db::{ExpandDatabase, HirDatabase},
    Adt, AssocItem, ClosureStyle, Const, ConstParam, Field, Function, GenericParam, HirDisplay,
    Impl, Local, Module, ModuleDef, ScopeDef, Semantics, Static, Struct, StructKind, Type, Variant, DefWithBody,
};
use ide_db::{
    assists::{Assist, AssistId, AssistKind, GroupLabel},
    label::Label,
    source_change::SourceChange,
    FxHashSet, RootDatabase,
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
            fixes(&ctx.sema, d),
        )
    };

    Diagnostic::new(DiagnosticCode::RustcHardError("typed-hole"), message, display_range.range)
        .with_fixes(fixes)
}

pub fn fixes(sema: &Semantics<'_, RootDatabase>, d: &hir::TypedHole) -> Option<Vec<Assist>> {
    let db = sema.db;
    let root = db.parse_or_expand(d.expr.file_id);
    let original_range =
        d.expr.as_ref().map(|it| it.to_node(&root)).syntax().original_file_range_opt(db)?;
    let scope = sema.scope(d.expr.value.to_node(&root).syntax())?;

    let mut names = Vec::default();
    let mut defs = FxHashSet::default();
    defs.insert(ScopeDef::ModuleDef(ModuleDef::Module(scope.module())));

    scope.process_all_names(&mut |name, def| {
        names.push(format!("{} - {:?}", name.display(db).to_string(), def));
        defs.insert(def);
    });

    let mut paths = dfs_term_search(&d.expected, &defs, db, 2);
    paths.sort_by(|(d1, _), (d2, _)| d1.cmp(d2));

    let mut assists = vec![];
    for (_d, path) in paths {
        let code = path.gen_source_code(&defs, sema);

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
    SelfParam(Impl),
}

impl TypeInhabitant {
    fn gen_source_code(
        &self,
        items_in_scope: &FxHashSet<ScopeDef>,
        sema: &Semantics<'_, RootDatabase>,
    ) -> String {
        let db = sema.db;
        let (name, module) = match self {
            TypeInhabitant::Const(it) => {
                let name = match it.name(db) {
                    Some(it) => it.display(db).to_string(),
                    None => String::from("_"),
                };
                (name, it.module(db))
            }
            TypeInhabitant::Static(it) => (it.name(db).display(db).to_string(), it.module(db)),
            TypeInhabitant::Local(it) => (it.name(db).display(db).to_string(), it.module(db)),
            TypeInhabitant::ConstParam(it) => (it.name(db).display(db).to_string(), it.module(db)),
            TypeInhabitant::SelfParam(_) => return String::from("self"),
        };
        let prefix = gen_module_prefix(module, items_in_scope, db);
        format!("{}{}", prefix, name)
    }

    fn ty(&self, db: &dyn HirDatabase) -> Type {
        match self {
            TypeInhabitant::Const(it) => it.ty(db),
            TypeInhabitant::Static(it) => it.ty(db),
            TypeInhabitant::Local(it) => it.ty(db),
            TypeInhabitant::ConstParam(it) => it.ty(db),
            TypeInhabitant::SelfParam(it) => it.self_ty(db),
        }
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
enum TypeTransformation {
    Function(Function),
    Variant(Variant),
    Struct(Struct),
    Field(Field),
}

fn gen_module_prefix(
    mut module: Module,
    items_in_scope: &FxHashSet<ScopeDef>,
    db: &dyn HirDatabase,
) -> String {
    let mut prefix = String::new();
    while !items_in_scope.contains(&ScopeDef::ModuleDef(ModuleDef::Module(module))) {
        match module.name(db) {
            Some(m) => prefix = format!("{}::{}", m.display(db.upcast()).to_string(), prefix),
            None => (),
        };
        match module.parent(db) {
            Some(m) => module = m,
            None => break,
        };
    }
    prefix
}

impl TypeTransformation {
    fn ret_ty(&self, db: &dyn HirDatabase) -> Type {
        match self {
            Self::Function(it) => it.ret_type(db),
            Self::Variant(it) => it.parent_enum(db).ty(db),
            Self::Struct(it) => it.ty(db),
            Self::Field(it) => it.ty(db),
        }
    }
    fn gen_source_code(
        &self,
        params: &[TypeTree],
        items_in_scope: &FxHashSet<ScopeDef>,
        sema: &Semantics<'_, RootDatabase>,
    ) -> String {
        let db = sema.db;
        match self {
            Self::Function(it) => {
                if it.has_self_param(db) {
                    let target = params
                        .first()
                        .expect("no self param")
                        .gen_source_code(items_in_scope, sema);
                    let args = params
                        .iter()
                        .skip(1)
                        .map(|f| f.gen_source_code(items_in_scope, sema))
                        .join(", ");
                    format!("{}.{}({})", target, it.name(db).display(db).to_string(), args)
                } else {
                    let args =
                        params.iter().map(|f| f.gen_source_code(items_in_scope, sema)).join(", ");
                    let sig = format!("{}({})", it.name(db).display(db).to_string(), args);
                    format!("{}{}", gen_module_prefix(it.module(db), items_in_scope, db), sig)
                }
            }
            Self::Variant(variant) => {
                let inner = match variant.kind(db) {
                    StructKind::Tuple => {
                        let args = params
                            .iter()
                            .map(|f| f.gen_source_code(items_in_scope, sema))
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
                                    a.gen_source_code(items_in_scope, sema)
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
                            a.gen_source_code(items_in_scope, sema)
                        )
                    })
                    .join(", ");
                let sig = format!("{} {{ {} }}", it.name(db).display(db).to_string(), args);
                format!("{}{}", gen_module_prefix(it.module(db), items_in_scope, db), sig)
            }
            Self::Field(it) => {
                let strukt = params
                    .first()
                    .expect("No params for struct field")
                    .gen_source_code(items_in_scope, sema);
                let field = it.name(db).display(db).to_string();
                format!("{strukt}.{field}")
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
        sema: &Semantics<'_, RootDatabase>,
    ) -> String {
        match self {
            TypeTree::TypeInhabitant(it) => it.gen_source_code(items_in_scope, sema),
            TypeTree::TypeTransformation { func, params } => {
                func.gen_source_code(&params, items_in_scope, sema)
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
    goal: &Type,
    defs: &FxHashSet<ScopeDef>,
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
                                let tts =
                                    dfs_term_search(param.ty(), defs, db, depth.saturating_sub(1));
                                let max = tts.iter().map(|(d, _)| *d).max().unwrap_or(0);
                                tts.into_iter().filter(|(d, _)| *d >= max).collect()
                            }))
                            .collect();

                    // let mut new_tts: Vec<(u32, TypeTree)> = param_trees
                    //     .into_iter()
                    //     .multi_cartesian_product()
                    //     .map(|params| {
                    //         (
                    //             params.iter().map(|(d, _)| *d).min().unwrap_or(0),
                    //             TypeTree::TypeTransformation {
                    //                 func: TypeTransformation::Function(func),
                    //                 params: params.into_iter().map(|(_, p)| p).collect(),
                    //             },
                    //         )
                    //     })
                    //     .collect();
                    let mut new_tts = build_permutations(
                        param_trees.into_iter(),
                        TypeTransformation::Function(func),
                    );

                    let rec_res: Vec<(u32, TypeTree)> = new_tts
                        .iter()
                        .flat_map(|(d, new_tt)| {
                            dfs_search_assoc_item(&new_tt, goal, defs, db, d.saturating_sub(1))
                                .into_iter()
                        })
                        .collect();

                    new_tts.extend(rec_res);
                    Some(new_tts)
                })
        })
        .flatten()
        .unique()
        .filter(|(_, tt)| tt.ty(db).could_unify_with_normalized(db, goal))
        .collect()
}

fn dfs_term_search(
    goal: &Type,
    defs: &FxHashSet<ScopeDef>,
    db: &dyn HirDatabase,
    depth: u32,
) -> Vec<(u32, TypeTree)> {
    if depth == 0 {
        return Vec::new();
    }

    let mut res = Vec::new();

    for def in defs {
        match def {
            ScopeDef::ModuleDef(ModuleDef::Const(it)) => {
                let tt = TypeTree::TypeInhabitant(TypeInhabitant::Const(*it));
                if it.ty(db).could_unify_with_normalized(db, goal) {
                    res.push((depth, tt));
                } else {
                    res.extend(dfs_search_assoc_item(&tt, goal, defs, db, depth.saturating_sub(1)));
                    res.extend(matching_struct_fields(db, &tt, goal, depth))
                }
            }
            ScopeDef::ModuleDef(ModuleDef::Static(it)) => {
                let tt = TypeTree::TypeInhabitant(TypeInhabitant::Static(*it));
                if it.ty(db).could_unify_with_normalized(db, goal) {
                    res.push((depth, tt));
                } else {
                    res.extend(dfs_search_assoc_item(&tt, goal, defs, db, depth.saturating_sub(1)));
                    res.extend(matching_struct_fields(db, &tt, goal, depth))
                }
            }
            ScopeDef::GenericParam(GenericParam::ConstParam(it)) => {
                if it.ty(db).could_unify_with_normalized(db, goal) {
                    res.push((depth, TypeTree::TypeInhabitant(TypeInhabitant::ConstParam(*it))));
                } else {
                    res.extend(dfs_search_assoc_item(
                        &TypeTree::TypeInhabitant(TypeInhabitant::ConstParam(*it)),
                        goal,
                        defs,
                        db,
                        depth.saturating_sub(1),
                    ));
                }
            }
            ScopeDef::Local(it) => {
                let tt = TypeTree::TypeInhabitant(TypeInhabitant::Local(*it));
                if it.ty(db).could_unify_with_normalized(db, goal) {
                    res.push((depth, tt));
                } else {
                    res.extend(dfs_search_assoc_item(&tt, goal, defs, db, depth.saturating_sub(1)));
                    res.extend(matching_struct_fields(db, &tt, goal, depth))
                }
            }
            ScopeDef::ImplSelfType(it) => {
                let tt = TypeTree::TypeInhabitant(TypeInhabitant::SelfParam(*it));
                if it.self_ty(db).could_unify_with_normalized(db, goal) {
                    res.push((depth, tt));
                } else {
                    // res.extend(dfs_search_assoc_item(&tt, goal, defs, db, depth.saturating_sub(1)));
                    // res.extend(matching_struct_fields(db, &tt, goal, depth))
                }
            }
            ScopeDef::ModuleDef(ModuleDef::Function(it)) => {
                if it.ret_type(db).could_unify_with_normalized(db, goal) {
                    let param_trees = it.assoc_fn_params(db).into_iter().map(|param| {
                        dfs_term_search(param.ty(), defs, db, depth.saturating_sub(1))
                    });
                    res.extend(build_permutations(param_trees, TypeTransformation::Function(*it)));
                }
                let def: DefWithBody = (*it).into();
                let res = db.borrowck(def.into());
                dbg!(res);
            }
            ScopeDef::ModuleDef(ModuleDef::Variant(it)) => {
                if it.parent_enum(db).ty(db).could_unify_with_normalized(db, goal) {
                    let param_trees = it.fields(db).into_iter().map(|field| {
                        dfs_term_search(&field.ty(db), defs, db, depth.saturating_sub(1))
                    });
                    res.extend(build_permutations(param_trees, TypeTransformation::Variant(*it)));
                }
            }
            ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Enum(it))) => {
                for variant in it.variants(db) {
                    if it.ty(db).could_unify_with_normalized(db, goal) {
                        let param_trees = variant.fields(db).into_iter().map(|field| {
                            dfs_term_search(&field.ty(db), defs, db, depth.saturating_sub(1))
                        });

                        res.extend(build_permutations(
                            param_trees,
                            TypeTransformation::Variant(variant),
                        ));
                    }
                }
            }
            ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Struct(it))) => {
                if it.ty(db).could_unify_with_normalized(db, goal) {
                    let param_trees = it.fields(db).into_iter().map(|strukt| {
                        dfs_term_search(&strukt.ty(db), defs, db, depth.saturating_sub(1))
                    });
                    res.extend(build_permutations(param_trees, TypeTransformation::Struct(*it)));
                }
            }
            _ => (),
        }
    }
    res.into_iter().unique().collect()
}

fn matching_struct_fields(
    db: &dyn HirDatabase,
    tt: &TypeTree,
    goal: &Type,
    depth: u32,
) -> Vec<(u32, TypeTree)> {
    tt.ty(db)
        .fields(db)
        .into_iter()
        .filter(|(_, ty)| ty.could_unify_with_normalized(db, goal))
        .map(|(field, _)| {
            (
                depth,
                TypeTree::TypeTransformation {
                    func: TypeTransformation::Field(field),
                    params: vec![tt.clone()],
                },
            )
        })
        .collect()
}

fn build_permutations(
    param_trees: impl Iterator<Item = Vec<(u32, TypeTree)>>,
    tt: TypeTransformation,
) -> Vec<(u32, TypeTree)> {
    // Extra case for transformations with 0 params
    let (param_trees, count_tree) = param_trees.tee();
    if count_tree.count() == 0 {
        return vec![(0, TypeTree::TypeTransformation { func: tt.clone(), params: Vec::new() })];
    }

    let mut max_depth = 0;
    param_trees
        .multi_cartesian_product()
        .filter_map(move |params| {
            let depth = params.iter().map(|(d, _)| *d).min().unwrap_or(0);
            if depth < max_depth {
                return None;
            }
            max_depth = depth;
            Some((
                depth,
                TypeTree::TypeTransformation {
                    func: tt.clone(),
                    params: params.into_iter().map(|(_, p)| p).collect(),
                },
            ))
        })
        .filter(|(d, _)| *d >= max_depth)
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::tests::{
        check_diagnostics, check_fixes_unordered, check_has_fix, check_has_single_fix,
    };

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
    let _x = [(); _];
    let _y: [(); 10] = [(); _];
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
        check_has_single_fix(
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

    #[test]
    fn test_find_reference_return() {
        check_has_fix(
            r#"
fn foo(a: i32) -> &i32 {
    &a
}
fn main() {
    let a: &i32 = &1;
    let c: &i32 = _$0;
}"#,
            r#"
fn main() {
    let a: &i32 = &1;
    let c: &i32 = xa;
}"#,
        );
    }
}
