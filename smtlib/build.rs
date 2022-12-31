use std::{
    fs::{self, File},
    io::Write,
};

use build_util::{
    itertools::Itertools,
    miette::{self, Context, IntoDiagnostic},
};
use smtlib_lowlevel::ast::{Logic, LogicAttribute};

fn logics() -> miette::Result<Vec<Logic>> {
    let mut logics = vec![];

    for p in fs::read_dir("../spec/logics").into_diagnostic()? {
        let p = p.into_diagnostic()?;
        let p = p.path();
        if let Some("smt2") = p.extension().and_then(|c| c.to_str()) {
            let s = build_util::read_to_string(&p)?;
            let l = Logic::parse(&s).with_context(|| format!("parsing {p:?}"))?;
            logics.push(l);
        }
    }

    Ok(logics)
}

fn main() -> miette::Result<()> {
    let out = build_util::out_dir();

    let mut logic_file = File::create(out.join("logic.rs")).unwrap();

    writeln!(
        logic_file,
        "
        #[allow(nonstandard_style)]
        pub enum Logic {{
        "
    )
    .into_diagnostic()?;

    let logics = logics()?;

    for Logic(name, attrs) in &logics {
        let language = attrs
            .iter()
            .find_map(|a| match a {
                LogicAttribute::Theories(_) => None,
                LogicAttribute::Language(l) => Some(l.clone()),
                LogicAttribute::Extensions(_) => None,
                LogicAttribute::Values(_) => None,
                LogicAttribute::Notes(_) => None,
                LogicAttribute::Attribute(_) => None,
            })
            .unwrap();
        let language = language
            .trim()
            .trim_matches(|c| c == '"' || c == '“')
            .lines()
            .map(|l| format!("/// {l}"))
            .format("\n");

        writeln!(logic_file, "{language}").into_diagnostic()?;
        writeln!(logic_file, "{name},").into_diagnostic()?;
    }

    writeln!(
        logic_file,
        "
            Custom(String),
        }}"
    )
    .into_diagnostic()?;

    let display_impl = logics
        .iter()
        .map(|Logic(name, _)| format!("Self::{name} => \"{name}\".fmt(f),"))
        .format("\n");

    writeln!(
        logic_file,
        r#"
        impl std::fmt::Display for Logic {{
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {{
                match self {{
                    {display_impl}
                    Self::Custom(s) => s.fmt(f),
                }}
            }}
        }}
    "#
    )
    .into_diagnostic()?;

    Ok(())
}
