use miette::{Context, IntoDiagnostic, Result};
use smtlib_lowlevel::{ast::Script, z3::Z3Binary, Driver};

fn main() -> Result<()> {
    miette::set_panic_hook();

    for p in std::env::args().skip(1) {
        let src = std::fs::read_to_string(&p).into_diagnostic()?;

        let script = Script::parse(&src).with_context(|| format!("parsing {p:?}"))?;

        let b = Z3Binary::new("z3").into_diagnostic()?;
        let mut d = Driver::new(b)?;
        for cmd in &script.0 {
            eprintln!("> {cmd}");
            let res = d.exec(cmd).into_diagnostic()?;
            println!("< {res}");
        }
    }

    Ok(())
}
