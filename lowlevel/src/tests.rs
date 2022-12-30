use crate::{ast::Script, lexicon::SmtlibParse, parse::Parser};

#[test]
fn escaped_string() {
    insta::assert_ron_snapshot!(String::parse(&mut Parser::new(
        r#""Hello ""world"" this is cool!""#
    )));
}

#[test]
fn bubble_sort() {
    insta::assert_ron_snapshot!(Script::parse(include_str!("../examples/bubble_sort.smt2")));
}
