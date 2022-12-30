use std::{
    collections::HashSet,
    io::{BufRead, Write},
};

use ast::{QualIdentifier, Term};
use parse::ParseError;

use crate::ast::{Command, GeneralResponse};

pub mod ast;
#[cfg(feature = "cvc5")]
pub mod cvc5;
pub mod lexicon;
mod parse;
#[cfg(test)]
mod tests;
#[cfg(feature = "z3")]
pub mod z3;

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

        driver.exec(&Command::SetOption(crate::ast::Option::PrintSuccess(true)))?;

        Ok(driver)
    }
    pub fn exec(&mut self, cmd: &Command) -> Result<GeneralResponse, Error> {
        writeln!(self.backend, "{cmd}")?;
        self.backend.flush()?;

        loop {
            let n = self.backend.read_line(&mut self.buf)?;
            if n == 0 {
                continue;
            }
            if self.buf.chars().filter(|c| *c == '(').count()
                != self.buf.chars().filter(|c| *c == ')').count()
            {
                continue;
            }
            if self.buf.ends_with('\n') {
                self.buf.pop();
            }

            match cmd {
                Command::Echo(_) if !self.buf.starts_with("(error") => {
                    self.buf.insert(0, '"');
                    self.buf.push('"');
                }
                _ => {}
            }
            // println!("<< {}", self.buf);
            let res = if cmd.has_response() {
                match cmd.parse_response(&self.buf) {
                    Ok(Some(res)) => GeneralResponse::SpecificSuccessResponse(res),
                    Ok(None) => GeneralResponse::parse(&self.buf)?,
                    Err(_) => GeneralResponse::parse(&self.buf)?,
                }
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
