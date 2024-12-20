#![deny(rustdoc::broken_intra_doc_links)]
#![allow(clippy::manual_async_fn)]

//! # smtlib-lowlevel
//!
//! _A low-level API for interacting with SMT solvers._

use std::collections::HashSet;

use ast::{QualIdentifier, Term};
use backend::Backend;
use parse::ParseError;

use crate::ast::{Command, GeneralResponse};

#[rustfmt::skip]
pub mod ast;
pub mod backend;
pub mod lexicon;
mod parse;
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
    fn exec(&self, cmd: &ast::Command);
    fn response(&self, cmd: &ast::Command, res: &str);
}

impl<F, G> Logger for (F, G)
where
    F: Fn(&ast::Command) + 'static,
    G: Fn(&ast::Command, &str) + 'static,
{
    fn exec(&self, cmd: &ast::Command) {
        (self.0)(cmd)
    }

    fn response(&self, cmd: &ast::Command, res: &str) {
        (self.1)(cmd, res)
    }
}

pub struct Driver<B> {
    backend: B,
    logger: Option<Box<dyn Logger>>,
}

impl<B: std::fmt::Debug> std::fmt::Debug for Driver<B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Driver")
            .field("backend", &self.backend)
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

impl<B> Driver<B>
where
    B: Backend,
{
    pub fn new(backend: B) -> Result<Self, Error> {
        let mut driver = Self {
            backend,
            logger: None,
        };

        driver.exec(&Command::SetOption(ast::Option::PrintSuccess(true)))?;

        Ok(driver)
    }

    pub fn set_logger(&mut self, logger: impl Logger) {
        self.logger = Some(Box::new(logger))
    }

    pub fn exec(&mut self, cmd: &Command) -> Result<GeneralResponse, Error> {
        if let Some(logger) = &self.logger {
            logger.exec(cmd);
        }
        let res = self.backend.exec(cmd)?;
        if let Some(logger) = &self.logger {
            logger.response(cmd, &res);
        }
        let res = if let Some(res) = cmd.parse_response(&res)? {
            GeneralResponse::SpecificSuccessResponse(res)
        } else {
            GeneralResponse::parse(&res)?
        };
        Ok(res)
    }
}

#[cfg(feature = "tokio")]
pub mod tokio {
    use crate::{
        Error, Logger,
        ast::{self, Command, GeneralResponse},
        backend::tokio::TokioBackend,
    };

    pub struct TokioDriver<B> {
        backend: B,
        logger: Option<Box<dyn Logger>>,
    }

    impl<B: std::fmt::Debug> std::fmt::Debug for TokioDriver<B> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_struct("TokioDriver")
                .field("backend", &self.backend)
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

    impl<B> TokioDriver<B>
    where
        B: TokioBackend,
    {
        pub async fn new(backend: B) -> Result<Self, Error> {
            let mut driver = Self {
                backend,
                logger: None,
            };

            driver
                .exec(&Command::SetOption(ast::Option::PrintSuccess(true)))
                .await?;

            Ok(driver)
        }

        pub fn set_logger(&mut self, logger: impl Logger) {
            self.logger = Some(Box::new(logger))
        }

        pub async fn exec(&mut self, cmd: &Command) -> Result<GeneralResponse, Error> {
            if let Some(logger) = &self.logger {
                logger.exec(cmd);
            }
            let res = self.backend.exec(cmd).await?;
            if let Some(logger) = &self.logger {
                logger.response(cmd, &res);
            }
            let res = if let Some(res) = cmd.parse_response(&res)? {
                GeneralResponse::SpecificSuccessResponse(res)
            } else {
                GeneralResponse::parse(&res)?
            };
            Ok(res)
        }
    }
}

// TODO: Use the definitions from 3.6.3 Scoping of variables and parameters
impl Term {
    pub fn all_consts(&self) -> HashSet<&QualIdentifier> {
        match self {
            Term::SpecConstant(_) => HashSet::new(),
            Term::Identifier(q) => std::iter::once(q).collect(),
            Term::Application(_, args) => args.iter().flat_map(|arg| arg.all_consts()).collect(),
            Term::Let(..) => todo!(),
            // TODO
            Term::Forall(..) => HashSet::new(),
            Term::Exists(..) => todo!(),
            Term::Match(..) => todo!(),
            Term::Annotation(..) => todo!(),
        }
    }

    pub fn strip_sort(self) -> Term {
        match self {
            Term::SpecConstant(_) => self,
            Term::Identifier(
                QualIdentifier::Identifier(ident) | QualIdentifier::Sorted(ident, _),
            ) => Term::Identifier(QualIdentifier::Identifier(ident)),
            Term::Application(
                QualIdentifier::Identifier(ident) | QualIdentifier::Sorted(ident, _),
                args,
            ) => {
                Term::Application(
                    QualIdentifier::Identifier(ident),
                    args.into_iter().map(|arg| arg.strip_sort()).collect(),
                )
            }
            Term::Let(..) => todo!(),
            Term::Forall(qs, rs) => Term::Forall(qs, rs),
            Term::Exists(..) => todo!(),
            Term::Match(..) => todo!(),
            Term::Annotation(..) => todo!(),
        }
    }
}
