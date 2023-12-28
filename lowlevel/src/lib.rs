#![deny(rustdoc::broken_intra_doc_links)]
#![allow(clippy::manual_async_fn)]

//! # smtlib-lowlevel
//!
//! _A low-level API for interacting with SMT solvers._

use std::collections::HashSet;

use ast::{QualIdentifier, Term};
use backend::{AsyncBackend, Backend};
use parse::ParseError;

use crate::ast::{Command, GeneralResponse};

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

#[derive(Debug)]
pub struct Driver<B> {
    backend: B,
}

impl<B> Driver<B>
where
    B: Backend,
{
    pub fn new(backend: B) -> Result<Self, Error> {
        let mut driver = Self { backend };

        driver.exec(&Command::SetOption(ast::Option::PrintSuccess(true)))?;

        Ok(driver)
    }
    pub fn exec(&mut self, cmd: &Command) -> Result<GeneralResponse, Error> {
        // println!("> {cmd}");
        let res = self.backend.exec(cmd)?;
        let res = if let Some(res) = cmd.parse_response(&res)? {
            GeneralResponse::SpecificSuccessResponse(res)
        } else {
            GeneralResponse::parse(&res)?
        };
        Ok(res)
    }
}

#[derive(Debug)]
pub struct AsyncDriver<B> {
    backend: B,
}

impl<B> AsyncDriver<B>
where
    B: AsyncBackend,
{
    pub async fn new(backend: B) -> Result<Self, Error> {
        let mut driver = Self { backend };

        driver
            .exec(&Command::SetOption(ast::Option::PrintSuccess(true)))
            .await?;

        Ok(driver)
    }
    pub async fn exec(&mut self, cmd: &Command) -> Result<GeneralResponse, Error> {
        // println!("> {cmd}");
        let res = self.backend.exec_async(cmd).await?;
        let res = if let Some(res) = cmd.parse_response(&res)? {
            GeneralResponse::SpecificSuccessResponse(res)
        } else {
            GeneralResponse::parse(&res)?
        };
        Ok(res)
    }
}

// TODO: Use the definitions from 3.6.3 Scoping of variables and parameters
impl Term {
    pub fn all_consts(&self) -> HashSet<&QualIdentifier> {
        match self {
            Term::SpecConstant(_) => HashSet::new(),
            Term::Identifier(q) => std::iter::once(q).collect(),
            Term::Application(q, args) => std::iter::once(q)
                .chain(args.iter().flat_map(|arg| arg.all_consts()))
                .collect(),
            Term::Let(_, _) => todo!(),
            // TODO
            Term::Forall(_, _) => HashSet::new(),
            Term::Exists(_, _) => todo!(),
            Term::Match(_, _) => todo!(),
            Term::Annotation(_, _) => todo!(),
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
            ) => Term::Application(
                QualIdentifier::Identifier(ident),
                args.into_iter().map(|arg| arg.strip_sort()).collect(),
            ),
            Term::Let(_, _) => todo!(),
            Term::Forall(qs, rs) => Term::Forall(qs, rs),
            Term::Exists(_, _) => todo!(),
            Term::Match(_, _) => todo!(),
            Term::Annotation(_, _) => todo!(),
        }
    }
}
