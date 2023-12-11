use hir::{db::ExpandDatabase, term_search::term_search, ClosureStyle, HirDisplay, Semantics};
use ide_db::{
    assists::{Assist, AssistId, AssistKind, GroupLabel},
    label::Label,
    source_change::SourceChange,
    RootDatabase,
};
use itertools::Itertools;
use text_edit::TextEdit;

use crate::{Diagnostic, DiagnosticCode, DiagnosticsContext};

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

    Diagnostic::new(DiagnosticCode::RustcHardError("typed-hole"), message, display_range)
        .with_fixes(fixes)
}

fn fixes(sema: &Semantics<'_, RootDatabase>, d: &hir::TypedHole) -> Option<Vec<Assist>> {
    let db = sema.db;
    let root = db.parse_or_expand(d.expr.file_id);
    let (original_range, _) =
        d.expr.as_ref().map(|it| it.to_node(&root)).syntax().original_file_range_opt(db)?;
    let scope = sema.scope(d.expr.value.to_node(&root).syntax())?;

    let paths = term_search(sema, &scope, &d.expected);

    let mut assists = vec![];
    for path in paths.into_iter().unique() {
        let code = path.gen_source_code(&scope);

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
    if !assists.is_empty() {
        Some(assists)
    } else {
        None
    }
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
     //^ 💡 error: invalid `_` expression, expected type `bool`
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
      //^ error: invalid `_` expression, expected type `&str`
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
    // FIXME: This should trigger error
    // let _y: [(); 10] = [(); _];
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
    Foo::foo(a)
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
    let c: Bar = Foo::foo(&a);
}"#,
        );
    }

    #[test]
    fn local_shadow_fn() {
        check_fixes_unordered(
            r#"
fn f() {
    let f: i32 = 0;
    _$0
}"#,
            vec![
                r#"
fn f() {
    let f: i32 = 0;
    ()
}"#,
                r#"
fn f() {
    let f: i32 = 0;
    crate::f()
}"#,
            ],
        );
    }
}
