use hir::HirDisplay;
use ide_db::assists::{AssistId, AssistKind};

use syntax::{ast, AstNode};

use crate::assist_context::{AssistContext, Assists};

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

    let param = ast::Expr::cast(syntax.clone());

    if param.is_none() {
        return acc.add(
            AssistId("term_search", AssistKind::Generate),
            "Term search",
            goal_range,
            |builder| {
                builder.replace(goal_range, format!("todo!(\"{}\")", "nono"));
            },
        );
    };

    let target_ty = ctx.sema.type_of_expr(&param.unwrap());
    let ty = if let Some(target_ty) = target_ty {
        format!("{}", target_ty.original().display(ctx.db()))
    } else {
        "none".to_string()
    };

    acc.add(AssistId("term_search", AssistKind::Generate), "Term search", goal_range, |builder| {
        builder.replace(goal_range, format!("todo!(\"{}\")", ty));
    })
}
