use hir::{
    db::HirDatabase, Adt, Const, Function, Local, ModuleDef, Static, Struct, StructKind, Type,
    Variant,
};
use hir::{HirDisplay, Module, ScopeDef};
use ide_db::assists::{AssistId, AssistKind};
use ide_db::FxHashSet;
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
    Variant(Variant),
    Struct(Struct),
}

impl TypeTransformation {
    fn could_unify_with(&self, db: &dyn HirDatabase, ty: &Type) -> bool {
        match self {
            Self::Function(it) => it.ret_type(db).could_unify_with(db, ty),
            Self::Variant(it) => it.parent_enum(db).ty(db).could_unify_with(db, ty),
            Self::Struct(it) => it.ty(db).could_unify_with(db, ty),
        }
    }

    fn gen_source_code(
        &self,
        params: &[TypeTree],
        items_in_scope: &FxHashSet<ScopeDef>,
        ctx: &AssistContext<'_>,
    ) -> String {
        let gen_module_prefix = |mut module: Module| {
            let mut prefix = String::new();
            while !items_in_scope.contains(&ScopeDef::ModuleDef(ModuleDef::Module(module))) {
                let mod_name = match module.name(ctx.db()) {
                    Some(m) => m.display(ctx.db()).to_string(),
                    None => String::from("<no_mod_name>")
                };
                prefix = format!("{}::{}", mod_name, prefix);
                match module.parent(ctx.db()) {
                   Some(m) => module = m,
                   None => break
                };
            }
            if prefix == "" {
                prefix
            } else {
                format!("{}::", prefix)
            }
        };
        match self {
            Self::Function(it) => {
                let args = params.iter().map(|f| f.gen_source_code(items_in_scope, ctx)).join(", ");
                let sig = format!("{}({})", it.name(ctx.db()).display(ctx.db()).to_string(), args);
                format!("{}{}", gen_module_prefix(it.module(ctx.db())), sig)
            }
            Self::Variant(variant) => {
                let inner = match variant.kind(ctx.db()) {
                    StructKind::Tuple => {
                        let args = params
                            .iter()
                            .map(|f| f.gen_source_code(items_in_scope, ctx))
                            .join(", ");
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
                                    a.gen_source_code(items_in_scope, ctx)
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
                if items_in_scope.contains(&ScopeDef::ModuleDef(ModuleDef::Variant(*variant))) {
                    inner
                } else {
                    let sig = format!(
                        "{}::{}",
                        variant.parent_enum(ctx.db()).name(ctx.db()).display(ctx.db()).to_string(),
                        inner,
                    );
                    format!("{}{}", gen_module_prefix(variant.module(ctx.db())), sig)
                }
            }
            Self::Struct(it) => {
                let fields = it.fields(ctx.db());
                let args = params
                    .iter()
                    .zip(fields.iter())
                    .map(|(a, f)| {
                        format!(
                            "{}: {}",
                            f.name(ctx.db()).display(ctx.db()).to_string(),
                            a.gen_source_code(items_in_scope, ctx)
                        )
                    })
                    .join(", ");
                let sig =
                    format!("{} {{ {} }}", it.name(ctx.db()).display(ctx.db()).to_string(), args);
                format!("{}{}", gen_module_prefix(it.module(ctx.db())), sig)
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
    let mut items_in_scope = FxHashSet::default();
    items_in_scope.insert(ScopeDef::ModuleDef(ModuleDef::Module(scope.module())));
    scope.process_all_names(&mut |name, def| {
        names.push(format!("{} - {:?}", name.display(ctx.db()).to_string(), def));
        items_in_scope.insert(def);
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
                let variants =
                    it.variants(ctx.db()).into_iter().map(|v| TypeTransformation::Variant(v));
                funcs.extend(variants);
            }
            ScopeDef::ModuleDef(ModuleDef::Adt(Adt::Struct(it))) => {
                funcs.push(TypeTransformation::Struct(it));
            }
            ScopeDef::Local(it) => {
                vars.push(TypeInhabitant::Local(it));
            }
            _ => {}
        }
    });

    let path = dfs_term_search(&target_ty, &vars, &funcs, ctx.db())?;

    acc.add(AssistId("term_search", AssistKind::Generate), "Term search", goal_range, |builder| {
        builder.replace(goal_range, path.gen_source_code(&items_in_scope, ctx));
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
    fn gen_source_code(
        &self,
        items_in_scope: &FxHashSet<ScopeDef>,
        ctx: &AssistContext<'_>,
    ) -> String {
        match self {
            TypeTree::TypeInhabitant(it) => match it {
                TypeInhabitant::Const(it) => it.name(ctx.db()).expect("Sum Ting Wong!?!"),
                TypeInhabitant::Static(it) => it.name(ctx.db()),
                TypeInhabitant::Local(it) => it.name(ctx.db()),
            }
            .display(ctx.db())
            .to_string(),
            TypeTree::TypeTransformation { func, params } => {
                func.gen_source_code(&params, items_in_scope, ctx)
            }
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
        funcs.iter().filter(|func| func.could_unify_with(db, goal)).find_map(|tt| match tt {
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

                let node = TypeTree::TypeTransformation { func: tt.clone(), params };
                Some(node)
            }
            TypeTransformation::Variant(variant) => {
                let fields: Vec<TypeTree> =
                    variant.fields(db).into_iter().fold(Some(Vec::new()), |acc, field| {
                        acc.and_then(|mut fields| {
                            dfs_term_search(&field.ty(db), vars, funcs, db).and_then(|field| {
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
                            dfs_term_search(&field.ty(db), vars, funcs, db).and_then(|field| {
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
