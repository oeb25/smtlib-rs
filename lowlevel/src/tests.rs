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

mod z3 {
    use crate::{Driver, ast::Command, backend::z3_binary::Z3Binary};

    macro_rules! cmd {
        ($d:expr, $cmd:literal) => {
            insta::assert_ron_snapshot!($d.exec(&Command::parse($cmd)?)?);
        };
    }

    #[test]
    fn echo_test() -> Result<(), Box<dyn std::error::Error>> {
        let mut d = Driver::new(Z3Binary::new("z3")?)?;

        cmd!(d, r#"(echo "Hello, world!")"#);
        cmd!(d, r#"(echo "Hello, unmatched paren! :)")"#);

        Ok(())
    }

    #[test]
    fn negative_numbers() -> Result<(), Box<dyn std::error::Error>> {
        let mut d = Driver::new(Z3Binary::new("z3")?)?;

        cmd!(d, r#"(declare-const x Int)"#);
        cmd!(d, r#"(assert (< x (- 1)))"#);
        cmd!(d, r#"(check-sat)"#);
        cmd!(d, r#"(get-model)"#);

        Ok(())
    }
}

#[cfg(feature = "z3-static")]
mod z3_static {
    use crate::{Driver, ast::Command, backend::Z3Static};

    macro_rules! cmd {
        ($d:expr, $cmd:literal) => {
            insta::assert_ron_snapshot!($d.exec(&Command::parse($cmd)?)?);
        };
    }

    #[test]
    fn echo_test() -> Result<(), Box<dyn std::error::Error>> {
        let mut d = Driver::new(Z3Static::new()?)?;

        cmd!(d, r#"(echo "Hello, world!")"#);
        cmd!(d, r#"(echo "Hello, unmatched paren! :)")"#);

        Ok(())
    }
}
