pub use itertools;
pub use miette;
use miette::{Context, IntoDiagnostic, Result};
use std::path::{Path, PathBuf};

pub mod spec;

pub fn out_dir() -> PathBuf {
    PathBuf::from(std::env::var("OUT_DIR").expect("Could not get OUT_DIR"))
}

pub fn env_var(key: &str) -> Result<String> {
    println!("cargo:rerun-if-env-changed={key}");
    std::env::var(key)
        .into_diagnostic()
        .with_context(|| format!("reading env var ${key}"))
}

pub fn read_to_string(path: impl AsRef<Path>) -> Result<String> {
    let path = path.as_ref();
    println!("cargo:rerun-if-changed={path:?}");
    std::fs::read_to_string(path).into_diagnostic()
}
