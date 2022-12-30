use std::{fs::File, path::PathBuf};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let out = PathBuf::from(std::env::var("OUT_DIR").expect("Could not get OUT_DIR"));

    let mut const_file = File::create(out.join("ast.rs")).unwrap();

    build_util::spec::generate(&mut const_file)?;

    Ok(())
}
