//! Backends are concrete solvers which can be communicated with using the
//! SMT-LIB language.
//!
//! This module contains the solver which are supported out-of-the-box by
//! `smtlib`. Each backend is feature gated, which means that a feature must be
//! enabled to use the backend.
//!
//! ## Backends
//!
//! - **[`Z3Binary`](z3_binary::Z3Binary)**: A [Z3](https://github.com/Z3Prover/z3)
//!   backend using the binary CLI interface.
//! - **[`Z3BinaryTokio`](z3_binary::tokio::Z3BinaryTokio)**: An async [Z3](https://github.com/Z3Prover/z3)
//!   backend using the binary CLI interface with [`tokio`](::tokio).
//!     - **Enabled by feature:** `tokio`
//! - **`Z3Static`**: A [Z3](https://github.com/Z3Prover/z3) backend using the [`z3-sys`
//!   crate](https://github.com/prove-rs/z3.rs).
//!     - **Enabled by feature:** `z3-static`
//! - **[`Cvc5Binary`](cvc5_binary::Cvc5Binary)**: A [cvc5](https://cvc5.github.io/)
//!   backend using the binary CLI interface.
//! - **[`Cvc5BinaryTokio`](cvc5_binary::tokio::Cvc5BinaryTokio)**: An async [cvc5](https://cvc5.github.io/)
//!   backend using the binary CLI interface with [`tokio`](::tokio).
//!     - **Enabled by feature:** `tokio`

use std::{
    io::{BufRead, BufReader, Write},
    process::{Child, ChildStdin, ChildStdout},
};

use logos::Lexer;

pub mod cvc5_binary;
pub mod z3_binary;
#[cfg(feature = "z3-static")]
pub mod z3_static;

use crate::parse::Token;

/// The [`Backend`] trait is used to interact with SMT solver using the SMT-LIB
/// language.
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
            if Lexer::new(self.buf.as_str())
                .map(|tok| tok.unwrap_or(Token::Error))
                .fold(0i32, |acc, tok| {
                    match tok {
                        Token::LParen => acc + 1,
                        Token::RParen => acc - 1,
                        _ => acc,
                    }
                })
                != 0
            {
                continue;
            }
            return Ok(&self.buf);
        }
    }
}

#[cfg(feature = "tokio")]
pub mod tokio {
    use std::future::Future;

    use logos::Lexer;
    use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};

    use crate::parse::Token;

    /// The [`TokioBackend`] trait is used to interact with SMT solver using the
    /// SMT-LIB language.
    ///
    /// For more details read the [`backend`](crate::backend) module
    /// documentation.
    pub trait TokioBackend {
        fn exec(
            &mut self,
            cmd: &crate::Command,
        ) -> impl Future<Output = Result<String, crate::Error>>;
    }

    pub(crate) struct TokioBinaryBackend {
        #[allow(unused)]
        child: tokio::process::Child,
        stdin: tokio::process::ChildStdin,
        stdout: BufReader<tokio::process::ChildStdout>,
        buf: String,
    }

    #[cfg(feature = "tokio")]
    impl TokioBinaryBackend {
        pub(crate) async fn new(
            program: impl AsRef<std::ffi::OsStr>,
            init: impl FnOnce(&mut tokio::process::Command),
        ) -> Result<Self, std::io::Error> {
            use std::process::Stdio;

            use tokio::process::Command;

            let mut cmd = Command::new(program);
            init(&mut cmd);
            let mut child = cmd
                .kill_on_drop(true)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .spawn()?;
            let stdin = child.stdin.take().unwrap();
            let stdout = BufReader::new(child.stdout.take().unwrap());

            Ok(TokioBinaryBackend {
                child,
                stdin,
                stdout,
                buf: String::new(),
            })
        }

        pub(crate) async fn exec(&mut self, cmd: &crate::Command) -> Result<&str, crate::Error> {
            // eprintln!("> {cmd}");
            self.stdin.write_all(cmd.to_string().as_bytes()).await?;
            self.stdin.write_all(b"\n").await?;
            self.stdin.flush().await?;

            self.buf.clear();
            loop {
                let n = self.stdout.read_line(&mut self.buf).await?;
                if n == 0 {
                    continue;
                }
                if Lexer::new(self.buf.as_str())
                    .map(|tok| tok.unwrap_or(Token::Error))
                    .fold(0i32, |acc, tok| {
                        match tok {
                            Token::LParen => acc + 1,
                            Token::RParen => acc - 1,
                            _ => acc,
                        }
                    })
                    != 0
                {
                    continue;
                }
                return Ok(&self.buf);
            }
        }
    }
}
