use hir::{db::HirDatabase, Const, Function, HirDisplay, Local, Static, Type};
use ide_db::assists::{AssistId, AssistKind};

use syntax::{ast, AstNode};

use crate::assist_context::{AssistContext, Assists};

#[derive(Clone, Eq, Hash, PartialEq)]
enum TypeInhabitant {
    Const(Const),
    Static(Static),
    Local(Local),
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
    scope.process_all_names(&mut |_name, def| match def {
        hir::ScopeDef::ModuleDef(hir::ModuleDef::Function(it)) => {
            funcs.push(it);
        }
        hir::ScopeDef::ModuleDef(hir::ModuleDef::Const(it)) => {
            vars.push(TypeInhabitant::Const(it));
        }
        hir::ScopeDef::ModuleDef(hir::ModuleDef::Static(it)) => {
            vars.push(TypeInhabitant::Static(it));
        }
        hir::ScopeDef::Local(it) => {
            vars.push(TypeInhabitant::Local(it));
        }
        _ => {}
    });

    let path = dfs_term_search(&target_ty, &vars, &funcs, ctx.db());

    acc.add(AssistId("term_search", AssistKind::Generate), "Term search", goal_range, |builder| {
        builder.replace(goal_range, format!("todo!(\"{}\")", target_ty.display(ctx.db())));
    })
}

enum Node {
    /// Leaf node
    TypeInhabitant(TypeInhabitant),
    /// Node with children
    Transformation { func: Function, params: Vec<Node> },
}

fn dfs_term_search(
    goal: &Type,
    vars: &[TypeInhabitant],
    funcs: &[Function],
    db: &dyn HirDatabase,
) -> Option<Node> {
    if let Some(ty) = vars.iter().find(|&ty| ty.could_unify_with(db, goal)) {
        return Some(Node::TypeInhabitant(ty.clone()));
    };

    let func = funcs.iter().filter(|func| func.ret_type(db).could_unify_with(db, goal)).find_map(
        |&func| {
            let params: Vec<Node> =
                func.assoc_fn_params(db).into_iter().fold(Some(Vec::new()), |acc, param| {
                    acc.and_then(|mut params| {
                        dfs_term_search(param.ty(), vars, funcs, db).and_then(|param| {
                            params.push(param);
                            Some(params)
                        })
                    })
                })?;

            let node = Node::Transformation { func, params };
            Some(node)
        },
    );

    func
}
