use smtlib_lowlevel::{ast, lexicon::Symbol};

use crate::{
    sorts::Sort,
    terms::{Dynamic, qual_ident},
};

#[derive(Debug)]
pub struct Fun {
    pub name: String,
    pub vars: Vec<Sort>,
    pub return_sort: Sort,
}

impl Fun {
    pub fn new(name: impl Into<String>, vars: Vec<Sort>, return_ty: Sort) -> Self {
        Self {
            name: name.into(),
            vars,
            return_sort: return_ty,
        }
    }

    pub fn call(&self, args: &[Dynamic]) -> Result<Dynamic, crate::Error> {
        if self.vars.len() != args.len() {
            todo!()
        }
        for (expected, given) in self.vars.iter().zip(args) {
            if expected != given.sort() {
                todo!("expected {expected:?} given {:?}", given.sort())
            }
        }
        let term = if args.is_empty() {
            ast::Term::Identifier(qual_ident(self.name.clone(), None))
        } else {
            ast::Term::Application(
                qual_ident(self.name.clone(), None),
                args.iter().map(|arg| (*arg).into()).collect(),
            )
        };
        Ok(Dynamic::from_term_sort(term, self.return_sort.clone()))
    }

    pub fn ast(&self) -> ast::FunctionDec {
        ast::FunctionDec(
            Symbol(self.name.to_string()),
            self.vars.iter().map(|sort| sort.ast()).collect(),
            self.return_sort.ast(),
        )
    }
}
