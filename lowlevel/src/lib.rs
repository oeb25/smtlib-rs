//! # smtlib-lowlevel
//!
//! _A low-level API for interacting with SMT solvers._

use std::{
    collections::HashSet,
    io::{BufRead, Write},
};

use ast::{QualIdentifier, Term};
use logos::Lexer;
use parse::{ParseError, Token};

use crate::ast::{Command, GeneralResponse};

pub mod ast;
pub mod backend;
pub mod lexicon;
mod parse;
#[cfg(test)]
mod tests;

#[derive(Debug)]
pub struct Driver<B> {
    backend: B,
    buf: String,
}

pub trait Backend: BufRead + Write {}

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

impl<B> Driver<B>
where
    B: Backend,
{
    pub fn new(backend: B) -> Result<Self, Error> {
        let mut driver = Self {
            backend,
            buf: Default::default(),
        };

        driver.exec(&Command::SetOption(ast::Option::PrintSuccess(true)))?;

        Ok(driver)
    }
    pub fn exec(&mut self, cmd: &Command) -> Result<GeneralResponse, Error> {
        println!("> {cmd}");
        writeln!(self.backend, "{cmd}")?;
        self.backend.flush()?;

        loop {
            let n = self.backend.read_line(&mut self.buf)?;
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
            let res = if let Some(res) = cmd.parse_response(&self.buf)? {
                GeneralResponse::SpecificSuccessResponse(res)
            } else {
                GeneralResponse::parse(&self.buf)?
            };
            self.buf.clear();
            return Ok(res);
        }
    }
}

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
