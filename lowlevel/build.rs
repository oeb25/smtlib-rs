use std::fs::File;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let out = smtlib_build_util::out_dir();

    let mut ast_file = File::create(out.join("ast.rs")).unwrap();

    smtlib_build_util::spec::generate(&mut ast_file)?;

    Ok(())
}
