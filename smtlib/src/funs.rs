use itertools::Itertools;
use smtlib_lowlevel::{ast, lexicon::Symbol, Storage};

use crate::{
    sorts::Sort,
    terms::{qual_ident, Dynamic, STerm},
    Sorted,
};

#[derive(Debug)]
pub struct Fun<'st> {
    pub st: &'st Storage,
    pub name: &'st str,
    pub vars: &'st [Sort<'st>],
    pub return_sort: Sort<'st>,
}

impl<'st> Fun<'st> {
    pub fn new(
        st: &'st Storage,
        name: impl Into<String>,
        vars: Vec<Sort<'st>>,
        return_ty: Sort<'st>,
    ) -> Self {
        Self {
            st,
            name: st.alloc_str(&name.into()),
            vars: st.alloc_slice(&vars),
            return_sort: return_ty,
        }
    }

    pub fn call(&self, args: &[Dynamic<'st>]) -> Result<Dynamic<'st>, crate::Error> {
        if self.vars.len() != args.len() {
            todo!()
        }
        for (expected, given) in self.vars.iter().zip(args) {
            if expected != given.sort() {
                todo!("expected {expected:?} given {:?}", given.sort())
            }
        }
        let term = if args.is_empty() {
            ast::Term::Identifier(qual_ident(self.name, None))
        } else {
            ast::Term::Application(
                qual_ident(self.name, None),
                self.st
                    .alloc_slice(&args.iter().map(|arg| arg.term()).collect_vec()),
            )
        };
        Ok(Dynamic::from_term_sort(
            STerm::new(self.st, term),
            self.return_sort,
        ))
    }

    pub fn ast(&self) -> ast::FunctionDec {
        ast::FunctionDec(
            Symbol(self.name),
            self.st
                .alloc_slice(&self.vars.iter().map(|sort| sort.ast()).collect_vec()),
            self.return_sort.ast(),
        )
    }
}
