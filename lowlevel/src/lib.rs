#![deny(rustdoc::broken_intra_doc_links)]
#![allow(clippy::manual_async_fn)]

//! # smtlib-lowlevel
//!
//! _A low-level API for interacting with SMT solvers._

use std::collections::HashSet;

use ast::{QualIdentifier, Term};
use backend::Backend;
use itertools::Itertools;
use parse::ParseError;

use crate::ast::{Command, GeneralResponse};
pub use crate::storage::Storage;

#[rustfmt::skip]
pub mod ast;
mod ast_ext;
pub mod backend;
pub mod lexicon;
mod parse;
mod storage;
#[cfg(test)]
mod tests;

#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum Error {
    #[error(transparent)]
    #[diagnostic(transparent)]
    Parse(
        #[from]
        #[diagnostic_source]
        ParseError,
    ),
    #[error(transparent)]
    IO(#[from] std::io::Error),
}

pub trait Logger: 'static {
    fn exec(&self, cmd: ast::Command);
    fn response(&self, cmd: ast::Command, res: &str);
}

impl<F, G> Logger for (F, G)
where
    F: Fn(ast::Command) + 'static,
    G: Fn(ast::Command, &str) + 'static,
{
    fn exec(&self, cmd: ast::Command) {
        (self.0)(cmd)
    }

    fn response(&self, cmd: ast::Command, res: &str) {
        (self.1)(cmd, res)
    }
}

pub struct Driver<'st, B> {
    st: &'st Storage,
    backend: B,
    logger: Option<Box<dyn Logger>>,
}

impl<B: std::fmt::Debug> std::fmt::Debug for Driver<'_, B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Driver")
            .field("backend", &self.backend)
            .field("st", &"...")
            .field(
                "logger",
                if self.logger.is_some() {
                    &"Some(...)"
                } else {
                    &"None"
                },
            )
            .finish()
    }
}

impl<'st, B> Driver<'st, B>
where
    B: Backend,
{
    pub fn new(st: &'st Storage, backend: B) -> Result<Self, Error> {
        let mut driver = Self {
            st,
            backend,
            logger: None,
        };

        driver.exec(Command::SetOption(ast::Option::PrintSuccess(true)))?;

        Ok(driver)
    }
    pub fn st(&self) -> &'st Storage {
        self.st
    }
    pub fn set_logger(&mut self, logger: impl Logger) {
        self.logger = Some(Box::new(logger))
    }
    pub fn exec(&mut self, cmd: Command<'st>) -> Result<GeneralResponse<'st>, Error> {
        if let Some(logger) = &self.logger {
            logger.exec(cmd);
        }
        let res = self.backend.exec(cmd)?;
        if let Some(logger) = &self.logger {
            logger.response(cmd, &res);
        }
        let res = if let Some(res) = cmd.parse_response(self.st, &res)? {
            GeneralResponse::SpecificSuccessResponse(res)
        } else {
            GeneralResponse::parse(self.st, &res)?
        };
        Ok(res)
    }
}

#[cfg(feature = "tokio")]
pub mod tokio {
    use crate::{
        ast::{self, Command, GeneralResponse},
        backend::tokio::TokioBackend,
        storage::Storage,
        Error, Logger,
    };

    pub struct TokioDriver<'st, B> {
        st: &'st Storage,
        backend: B,
        logger: Option<Box<dyn Logger>>,
    }

    impl<B: std::fmt::Debug> std::fmt::Debug for TokioDriver<'_, B> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_struct("TokioDriver")
                .field("backend", &self.backend)
                .field("st", &"...")
                .field(
                    "logger",
                    if self.logger.is_some() {
                        &"Some(...)"
                    } else {
                        &"None"
                    },
                )
                .finish()
        }
    }

    impl<'st, B> TokioDriver<'st, B>
    where
        B: TokioBackend,
    {
        pub async fn new(st: &'st Storage, backend: B) -> Result<Self, Error> {
            let mut driver = Self {
                st,
                backend,
                logger: None,
            };

            driver
                .exec(Command::SetOption(ast::Option::PrintSuccess(true)))
                .await?;

            Ok(driver)
        }
        pub fn st(&self) -> &'st Storage {
            self.st
        }
        pub fn set_logger(&mut self, logger: impl Logger) {
            self.logger = Some(Box::new(logger))
        }
        pub async fn exec(&mut self, cmd: Command<'st>) -> Result<GeneralResponse<'st>, Error> {
            if let Some(logger) = &self.logger {
                logger.exec(cmd);
            }
            let res = self.backend.exec(cmd).await?;
            if let Some(logger) = &self.logger {
                logger.response(cmd, &res);
            }
            let res = if let Some(res) = cmd.parse_response(self.st, &res)? {
                GeneralResponse::SpecificSuccessResponse(res)
            } else {
                GeneralResponse::parse(self.st, &res)?
            };
            Ok(res)
        }
    }
}

// TODO: Use the definitions from 3.6.3 Scoping of variables and parameters
impl<'st> Term<'st> {
    pub fn all_consts(&self) -> HashSet<&QualIdentifier<'st>> {
        match self {
            Term::SpecConstant(_) => HashSet::new(),
            Term::Identifier(q) => std::iter::once(q).collect(),
            Term::Application(_, args) => args.iter().flat_map(|arg| arg.all_consts()).collect(),
            Term::Let(_, _) => todo!(),
            // TODO
            Term::Forall(_, _) => HashSet::new(),
            Term::Exists(_, _) => todo!(),
            Term::Match(_, _) => todo!(),
            Term::Annotation(_, _) => todo!(),
        }
    }
    pub fn strip_sort(&'st self, st: &'st Storage) -> &'st Term<'st> {
        match self {
            Term::SpecConstant(_) => self,
            Term::Identifier(
                QualIdentifier::Identifier(ident) | QualIdentifier::Sorted(ident, _),
            ) => st.alloc(Term::Identifier(QualIdentifier::Identifier(*ident))),
            Term::Application(
                QualIdentifier::Identifier(ident) | QualIdentifier::Sorted(ident, _),
                args,
            ) => st.alloc(Term::Application(
                QualIdentifier::Identifier(*ident),
                st.alloc_slice(&args.iter().map(|arg| arg.strip_sort(st)).collect_vec()),
            )),
            Term::Let(_, _) => todo!(),
            Term::Forall(qs, rs) => st.alloc(Term::Forall(qs, rs)),
            Term::Exists(_, _) => todo!(),
            Term::Match(_, _) => todo!(),
            Term::Annotation(_, _) => todo!(),
        }
    }
}
