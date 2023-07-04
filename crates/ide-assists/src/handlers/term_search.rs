use hir::HirDisplay;
use hir::{db::HirDatabase, Adt, Const, Function, Local, Static, StructKind, Type, Variant};
use ide_db::assists::{AssistId, AssistKind};
use itertools::Itertools;

use syntax::{ast, AstNode};

use crate::assist_context::{AssistContext, Assists};

#[derive(Clone, Eq, Hash, PartialEq)]
enum TypeInhabitant {
    Const(Const),
    Static(Static),
    Local(Local),
}

#[derive(Clone, Eq, Hash, PartialEq)]
enum TypeTransformation {
    Function(Function),
    Variant { variant: Variant, in_scope: bool },
}

impl TypeTransformation {
    fn could_unify_with(&self, db: &dyn HirDatabase, ty: &Type) -> bool {
        match self {
            Self::Function(it) => it.ret_type(db).could_unify_with(db, ty),
            Self::Variant { variant, .. } => {
                variant.parent_enum(db).ty(db).could_unify_with(db, ty)
            }
        }
    }

    fn gen_source_code(&self, params: &[TypeTree], ctx: &AssistContext<'_>) -> String {
        match self {
            TypeTransformation::Function(it) => {
                let args = params.iter().map(|f| f.gen_source_code(ctx)).join(", ");
                format!("{}({})", it.name(ctx.db()).display(ctx.db()).to_string(), args)
            }
            TypeTransformation::Variant { variant, in_scope } => {
                let inner = match variant.kind(ctx.db()) {
                    StructKind::Tuple => {
                        let args = params.iter().map(|f| f.gen_source_code(ctx)).join(", ");
                        format!(
                            "{}({})",
                            variant.name(ctx.db()).display(ctx.db()).to_string(),
                            args
                        )
                    }
                    StructKind::Record => {
                        let fields = variant.fields(ctx.db());
                        let args = params
                            .iter()
                            .zip(fields.iter())
                            .map(|(a, f)| {
                                format!(
                                    "{}: {}",
                                    f.name(ctx.db()).display(ctx.db()).to_string(),
                                    a.gen_source_code(ctx)
                                )
                            })
                            .join(", ");
                        format!(
                            "{} {{ {} }}",
                            variant.name(ctx.db()).display(ctx.db()).to_string(),
                            args
                        )
                    }
                    StructKind::Unit => variant.name(ctx.db()).display(ctx.db()).to_string(),
                };
                if *in_scope {
                    inner
                } else {
                    format!(
                        "{}::{}",
                        variant.parent_enum(ctx.db()).name(ctx.db()).display(ctx.db()).to_string(),
                        inner
                    )
                }
            }
        }
    }
}

impl TypeInhabitant {
    fn could_unify_with(&self, db: &dyn HirDatabase, ty: &Type) -> bool {
        let self_ty = match self {
            Self::Const(it) => it.ty(db),
            Self::Static(it) => it.ty(db),
            Self::Local(it) => it.ty(db),
        };
        self_ty.could_unify_with(db, ty)
    }
}

pub(crate) fn term_search(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    let unexpanded = ctx.find_node_at_offset::<ast::MacroCall>()?;
    let syntax = unexpanded.syntax();
    let goal_range = syntax.text_range();

    let excl = unexpanded.excl_token()?;
    let macro_name_token = excl.prev_token()?;
    let name = macro_name_token.text();
    if name != "todo" {
        return None;
    }

    let parent = syntax.parent()?;
    let target_ty = ctx.sema.type_of_expr(&ast::Expr::cast(parent.clone())?)?.adjusted();

    let scope = ctx.sema.scope(&parent)?;

    let mut funcs = Vec::default();
    let mut vars = Vec::default();
    let mut names = Vec::default();
    scope.process_all_names(&mut |name, def| {
        names.push(format!("{} - {:?}", name.display(ctx.db()).to_string(), def));
        match def {
            hir::ScopeDef::ModuleDef(hir::ModuleDef::Function(it)) => {
                funcs.push(TypeTransformation::Function(it));
            }
            hir::ScopeDef::ModuleDef(hir::ModuleDef::Const(it)) => {
                vars.push(TypeInhabitant::Const(it));
            }
            hir::ScopeDef::ModuleDef(hir::ModuleDef::Static(it)) => {
                vars.push(TypeInhabitant::Static(it));
            }
            hir::ScopeDef::ModuleDef(hir::ModuleDef::Variant(it)) => {
                funcs.push(TypeTransformation::Variant { variant: it, in_scope: true });
            }
            hir::ScopeDef::ModuleDef(hir::ModuleDef::Adt(Adt::Enum(it))) => {
                let variants = it
                    .variants(ctx.db())
                    .into_iter()
                    .map(|v| TypeTransformation::Variant { variant: v, in_scope: false });
                funcs.extend(variants);
            }
            hir::ScopeDef::Local(it) => {
                vars.push(TypeInhabitant::Local(it));
            }
            _ => {}
        }
    });

    let path = dfs_term_search(&target_ty, &vars, &funcs, ctx.db())?;

    // let a: i32 = todo!();

    acc.add(AssistId("term_search", AssistKind::Generate), "Term search", goal_range, |builder| {
        builder.replace(goal_range, path.gen_source_code(ctx));
    })
}

enum TypeTree {
    /// Leaf node
    TypeInhabitant(TypeInhabitant),
    /// Node with children
    TypeTransformation { func: TypeTransformation, params: Vec<TypeTree> },
}

impl TypeTree {
    /// TODO: Should not be optional
    fn gen_source_code(&self, ctx: &AssistContext<'_>) -> String {
        match self {
            TypeTree::TypeInhabitant(it) => match it {
                TypeInhabitant::Const(it) => it.name(ctx.db()).expect("Sum Ting Wong!?!"),
                TypeInhabitant::Static(it) => it.name(ctx.db()),
                TypeInhabitant::Local(it) => it.name(ctx.db()),
            }
            .display(ctx.db())
            .to_string(),
            TypeTree::TypeTransformation { func, params } => func.gen_source_code(&params, ctx),
        }
    }
}

fn dfs_term_search(
    goal: &Type,
    vars: &[TypeInhabitant],
    funcs: &[TypeTransformation],
    db: &dyn HirDatabase,
) -> Option<TypeTree> {
    if let Some(ty) = vars.iter().find(|&ty| ty.could_unify_with(db, goal)) {
        return Some(TypeTree::TypeInhabitant(ty.clone()));
    };

    let func =
        funcs.iter().filter(|func| func.could_unify_with(db, goal)).find_map(|func| match func {
            TypeTransformation::Function(func) => {
                let params: Vec<TypeTree> =
                    func.assoc_fn_params(db).into_iter().fold(Some(Vec::new()), |acc, param| {
                        acc.and_then(|mut params| {
                            dfs_term_search(param.ty(), vars, funcs, db).and_then(|param| {
                                params.push(param);
                                Some(params)
                            })
                        })
                    })?;

                let node = TypeTree::TypeTransformation {
                    func: TypeTransformation::Function(*func),
                    params,
                };
                Some(node)
            }
            TypeTransformation::Variant { variant, in_scope } => {
                let fields: Vec<TypeTree> =
                    variant.fields(db).into_iter().fold(Some(Vec::new()), |acc, field| {
                        acc.and_then(|mut fields| {
                            dfs_term_search(&field.ty(db), vars, funcs, db).and_then(|field| {
                                fields.push(field);
                                Some(fields)
                            })
                        })
                    })?;

                let node = TypeTree::TypeTransformation {
                    func: TypeTransformation::Variant { variant: *variant, in_scope: *in_scope },
                    params: fields,
                };
                Some(node)
            }
        });

    func
}
