//! Backends are concrete solvers which can be communicated with using the
//! SMT-LIB language.
//!
//! This module contains the solver which are supported out-of-the-box by
//! `smtlib`. Each backend is feature gated, which means that a feature must be
//! enabled to use the backend.
//!
//! ## Backends
//!
//! - **[`Z3Binary`]**: A [Z3](https://github.com/Z3Prover/z3) backend using the binary CLI interface.
//!     - **Enabled by feature:** `z3`
//! - **[`Z3Static`]**: A [Z3](https://github.com/Z3Prover/z3) backend using the [`z3-sys` crate](https://github.com/prove-rs/z3.rs).
//!     - **Enabled by feature:** `z3-static`
//! - **[`Cvc5Binary`]**: A [cvc5](https://cvc5.github.io/) backend using the binary CLI interface.
//!     - **Enabled by feature:** `cvc5`

use std::{
    io::{BufRead, BufReader, Write},
    process::{Child, ChildStdin, ChildStdout},
};

#[cfg(feature = "cvc5")]
mod cvc5;
#[cfg(feature = "cvc5")]
pub use cvc5::*;

#[cfg(feature = "z3")]
mod z3_binary;
use logos::Lexer;
#[cfg(feature = "z3")]
pub use z3_binary::*;

#[cfg(feature = "z3-static")]
mod z3_static;
#[cfg(feature = "z3-static")]
pub use z3_static::*;

use crate::parse::Token;

/// The [`Backend`] trait is used to interact with SMT solver using the SMT-LIB language.
///
/// For more details read the [`backend`](crate::backend) module documentation.
pub trait Backend {
    fn exec(&mut self, cmd: &crate::Command) -> Result<String, crate::Error>;
}

struct BinaryBackend {
    #[allow(unused)]
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    buf: String,
}

impl BinaryBackend {
    pub(crate) fn new(
        program: impl AsRef<std::ffi::OsStr>,
        init: impl FnOnce(&mut std::process::Command),
    ) -> Result<Self, std::io::Error> {
        use std::process::{Command, Stdio};

        let mut cmd = Command::new(program);
        init(&mut cmd);
        let mut child = cmd.stdin(Stdio::piped()).stdout(Stdio::piped()).spawn()?;
        let stdin = child.stdin.take().unwrap();
        let stdout = BufReader::new(child.stdout.take().unwrap());

        Ok(BinaryBackend {
            child,
            stdin,
            stdout,
            buf: String::new(),
        })
    }
    pub(crate) fn exec(&mut self, cmd: &crate::Command) -> Result<&str, crate::Error> {
        // println!("> {cmd}");
        writeln!(self.stdin, "{cmd}")?;
        self.stdin.flush()?;

        self.buf.clear();
        loop {
            let n = self.stdout.read_line(&mut self.buf)?;
            if n == 0 {
                continue;
            }
            if Lexer::new(self.buf.as_str()).fold(0i32, |acc, tok| match tok {
                Token::LParen => acc + 1,
                Token::RParen => acc - 1,
                _ => acc,
            }) != 0
            {
                continue;
            }
            return Ok(&self.buf);
        }
    }
}
