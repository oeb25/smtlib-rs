use crate::{ast::Script, lexicon::SmtlibParse, parse::Parser, storage::Storage};

#[test]
fn escaped_string() {
    let st = Storage::new();
    insta::assert_ron_snapshot!(String::parse(&mut Parser::new(
        &st,
        r#""Hello ""world"" this is cool!""#
    )));
}

#[test]
fn bubble_sort() {
    let st = Storage::new();
    insta::assert_ron_snapshot!(Script::parse(
        &st,
        include_str!("../examples/bubble_sort.smt2")
    ));
}

mod z3 {
    use crate::{ast::Command, backend::z3_binary::Z3Binary, storage::Storage, Driver};

    macro_rules! cmd {
        ($st:expr, $d:expr, $cmd:literal) => {
            insta::assert_ron_snapshot!($d.exec(Command::parse(&$st, $cmd)?)?);
        };
    }

    #[test]
    fn echo_test() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let mut d = Driver::new(&st, Z3Binary::new("z3")?)?;

        cmd!(st, d, r#"(echo "Hello, world!")"#);
        cmd!(st, d, r#"(echo "Hello, unmatched paren! :)")"#);

        Ok(())
    }

    #[test]
    fn negative_numbers() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let mut d = Driver::new(&st, Z3Binary::new("z3")?)?;

        cmd!(st, d, r#"(declare-const x Int)"#);
        cmd!(st, d, r#"(assert (< x (- 1)))"#);
        cmd!(st, d, r#"(check-sat)"#);
        cmd!(st, d, r#"(get-model)"#);

        Ok(())
    }
}

#[cfg(feature = "z3-static")]
mod z3_static {
    use crate::{ast::Command, backend::Z3Static, Driver};

    macro_rules! cmd {
        ($d:expr, $cmd:literal) => {
            insta::assert_ron_snapshot!($d.exec(&Command::parse($cmd)?)?);
        };
    }

    #[test]
    fn echo_test() -> Result<(), Box<dyn std::error::Error>> {
        let mut d = Driver::new(Z3Static::new()?)?;

        cmd!(st, d, r#"(echo "Hello, world!")"#);
        cmd!(st, d, r#"(echo "Hello, unmatched paren! :)")"#);

        Ok(())
    }
}
