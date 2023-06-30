use hir::{Const, HirDisplay, Local, Static};
use ide_db::{
    assists::{AssistId, AssistKind},
    FxHashSet,
};

use syntax::{ast, AstNode};

use crate::assist_context::{AssistContext, Assists};

#[derive(Eq, Hash, PartialEq)]
enum TypeInhabitant {
    Const(Const),
    Static(Static),
    Local(Local),
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

    let mut funcs = FxHashSet::default();
    let mut vars = FxHashSet::default();
    scope.process_all_names(&mut |_name, def| match def {
        hir::ScopeDef::ModuleDef(hir::ModuleDef::Function(it)) => {
            funcs.insert(it);
        }
        hir::ScopeDef::ModuleDef(hir::ModuleDef::Const(it)) => {
            vars.insert(TypeInhabitant::Const(it));
        }
        hir::ScopeDef::ModuleDef(hir::ModuleDef::Static(it)) => {
            vars.insert(TypeInhabitant::Static(it));
        }
        hir::ScopeDef::ModuleDef(_) => {}
        hir::ScopeDef::AdtSelfType(_) => {}
        hir::ScopeDef::Local(it) => {
            vars.insert(TypeInhabitant::Local(it));
        }
        _ => {}
    });

    let mut seen_methods = FxHashSet::default();
    target_ty.iterate_method_candidates_with_traits(
        ctx.db(),
        &scope,
        &scope.visible_traits(),
        None,
        None,
        |func| {
            if func.ret_type(ctx.db()) == target_ty {
                seen_methods.insert(func.name(ctx.db()));
            }
            None::<()>
        },
    );

    acc.add(AssistId("term_search", AssistKind::Generate), "Term search", goal_range, |builder| {
        builder.replace(goal_range, format!("todo!(\"{}\")", target_ty.display(ctx.db())));
    })
}
