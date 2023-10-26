use hir::{ModuleDef, ScopeDef};
use ide_db::{
    assists::{AssistId, AssistKind},
    FxHashSet,
};

use itertools::Itertools;
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

    let parent = syntax.parent()?;
    dbg!(ast::Expr::cast(parent.clone()), ctx.sema.type_of_expr(&ast::Expr::cast(parent.clone())?));
    let target_ty = ctx.sema.type_of_expr(&ast::Expr::cast(parent.clone())?)?.adjusted();

    let scope = ctx.sema.scope(&parent)?;

    let mut defs = FxHashSet::default();
    defs.insert(ScopeDef::ModuleDef(ModuleDef::Module(scope.module())));

    scope.process_all_names(&mut |_, def| {
        defs.insert(def);
    });

    let paths =
        hir::term_search::term_search(ctx.sema.db, scope.module(), defs.clone(), &target_ty);

    dbg!(&paths);

    if paths.is_empty() {
        return None;
    }

    for path in paths.iter().unique() {
        acc.add(
            AssistId("term_search", AssistKind::Generate),
            "Term search",
            goal_range,
            |builder| {
                builder.replace(goal_range, path.gen_source_code(&defs, &ctx.sema));
            },
        );
    }

    Some(())
}

#[cfg(test)]
mod tests {
    // use crate::tests::check_assist;

    // use super::*;

    #[test]
    fn test_complete_local() {
        // BUG: Macro expansion fails causing no target type
        // check_assist(
        //     term_search,
        //     "fn foo() -> u128 { let i: u128 = 1; todo$0!() }",
        //     "fn foo() -> u128 { let i: u128 = 1; i }",
        // )
    }
}
