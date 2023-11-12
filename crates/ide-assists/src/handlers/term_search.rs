use hir::{ModuleDef, ScopeDef};
use ide_db::{
    assists::{AssistId, AssistKind, GroupLabel},
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
    let target_ty = ctx.sema.type_of_expr(&ast::Expr::cast(parent.clone())?)?.adjusted();

    let scope = ctx.sema.scope(&parent)?;

    let mut defs = FxHashSet::default();
    defs.insert(ScopeDef::ModuleDef(ModuleDef::Module(scope.module())));

    scope.process_all_names(&mut |_, def| {
        defs.insert(def);
    });

    let paths = hir::term_search::term_search(&ctx.sema, scope.module(), defs.clone(), &target_ty);

    dbg!(&paths);

    if paths.is_empty() {
        return None;
    }

    for path in paths.iter().unique() {
        acc.add_group(
            &GroupLabel(String::from("term_search")),
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
    use crate::tests::check_assist;

    use super::*;

    #[test]
    fn test_complete_local() {
        check_assist(
            term_search,
            "macro_rules! todo { () => (_) }; fn f() { let a: u128 = 1; let b: u128 = todo$0!() }",
            "macro_rules! todo { () => (_) }; fn f() { let a: u128 = 1; let b: u128 = a }",
        )
    }

    #[test]
    fn test_complete_todo_with_msg() {
        check_assist(
            term_search,
            "macro_rules! todo { ($($arg:tt)+) => (_) }; fn f() { let a: u128 = 1; let b: u128 = todo$0!(\"asd\") }",
            "macro_rules! todo { ($($arg:tt)+) => (_) }; fn f() { let a: u128 = 1; let b: u128 = a }",
        )
    }

    #[test]
    fn test_complete_struct_field() {
        check_assist(
            term_search,
            r#"macro_rules! todo { () => (_) };
            struct A { pub x: i32, y: bool }
            fn f() { let a = A { x: 1, y: true }; let b: i32 = todo$0!(); }"#,
            r#"macro_rules! todo { () => (_) };
            struct A { pub x: i32, y: bool }
            fn f() { let a = A { x: 1, y: true }; let b: i32 = a.x; }"#,
        )
    }

    #[test]
    fn test_enum_with_generics() {
        check_assist(
            term_search,
            r#"macro_rules! todo { () => (_) };
            enum Option<T> { Some(T), None }
            fn f() { let a: i32 = 1; let b: Option<i32> = todo$0!(); }"#,
            r#"macro_rules! todo { () => (_) };
            enum Option<T> { Some(T), None }
            fn f() { let a: i32 = 1; let b: Option<i32> = Option::<i32>::None; }"#,
        )
    }

    #[test]
    fn test_enum_with_generics2() {
        check_assist(
            term_search,
            r#"macro_rules! todo { () => (_) };
            enum Option<T> { None, Some(T) }
            fn f() { let a: i32 = 1; let b: Option<i32> = todo$0!(); }"#,
            r#"macro_rules! todo { () => (_) };
            enum Option<T> { None, Some(T) }
            fn f() { let a: i32 = 1; let b: Option<i32> = Option::<i32>::Some(a); }"#,
        )
    }
}
