//! SMT sorts.
//!
//! From SMT-LIB reference:
//!
//! > A major subset of the SMT-LIB language is the language of well-sorted
//! > terms, used to represent logical expressions. Such terms are typed, or
//! > sorted in logical terminology; that is, each is associated with a (unique)
//! > sort. The set of sorts consists itself of sort terms. In essence, a sort
//! > term is a sort symbol, a sort parameter, or a sort symbol applied to a
//! > sequence of sort terms.

use itertools::Itertools;
use smtlib_lowlevel::{
    ast::{self, Identifier},
    lexicon::{Numeral, Symbol},
    Storage,
};

use crate::terms::{self, qual_ident, STerm};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SortTemplate<'st> {
    pub st: &'st Storage,
    pub name: &'st str,
    pub index: &'st [Index<'st>],
    pub arity: usize,
}

/// A SMT-LIB sort.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sort<'st> {
    /// A built-in sort.
    Static {
        /// The name of the sort.
        name: &'static str,
        /// The index of the sort.
        index: &'static [smtlib_lowlevel::ast::Index<'static>],
    },
    /// A user-defined sort.
    Dynamic {
        /// smtlib storage
        st: &'st Storage,
        /// The name of the sort.
        name: &'st str,
        /// The index of the sort.
        index: &'st [Index<'st>],
        /// The parameters of the sort.
        parameters: &'st [Sort<'st>],
    },
}

impl std::fmt::Display for Sort<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.ast().fmt(f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Index<'st> {
    Numeral(usize),
    Symbol(&'st str),
}

impl<'st> SortTemplate<'st> {
    pub fn instantiate(&self, parameters: &[Sort<'st>]) -> Result<Sort<'st>, crate::Error> {
        if self.arity != parameters.len() {
            return Err(todo!());
        }

        Ok(Sort::Dynamic {
            st: self.st,
            name: self.name,
            index: self.index,
            parameters: self.st.alloc_slice(parameters),
        })
    }
}

impl<'st> Index<'st> {
    fn ast(&self, st: &'st Storage) -> ast::Index<'st> {
        match self {
            Index::Numeral(n) => ast::Index::Numeral(Numeral(st.alloc_str(&n.to_string()))),
            Index::Symbol(s) => ast::Index::Symbol(Symbol(s)),
        }
    }
}

pub(crate) fn is_built_in_sort(name: &str) -> bool {
    matches!(name, "Int" | "Bool" | "Array" | "BitVec")
}

impl<'st> Sort<'st> {
    pub fn new_static(
        name: &'static str,
        index: &'static [smtlib_lowlevel::ast::Index<'static>],
    ) -> Self {
        Sort::Static { name, index }
    }
    pub fn new(st: &'st Storage, name: impl Into<String>) -> Self {
        let mut name = name.into();
        if !is_built_in_sort(&name) {
            // HACK: how should we handle this? or should we event handle it?
            name += "_xxx";
        }
        let name = st.alloc_str(&name);
        Self::Dynamic {
            st,
            name,
            index: &[],
            parameters: &[],
        }
    }
    pub fn new_parametric(
        st: &'st Storage,
        name: impl Into<String>,
        parameters: &[Sort<'st>],
    ) -> Self {
        Self::Dynamic {
            st,
            name: st.alloc_str(&name.into()),
            index: &[],
            parameters: st.alloc_slice(parameters),
        }
    }
    pub fn new_indexed(st: &'st Storage, name: impl Into<String>, index: &[Index<'st>]) -> Self {
        Self::Dynamic {
            st,
            name: st.alloc_str(&name.into()),
            index: st.alloc_slice(index),
            parameters: &[],
        }
    }

    pub fn ast(&self) -> ast::Sort<'st> {
        match self {
            Sort::Static { name, index } => {
                if index.is_empty() {
                    ast::Sort::Sort(Identifier::Simple(Symbol(name)))
                } else {
                    ast::Sort::Sort(Identifier::Indexed(Symbol(name), index))
                }
            }
            Sort::Dynamic {
                st,
                name,
                index,
                parameters,
            } => {
                let ident = if index.is_empty() {
                    Identifier::Simple(Symbol(name))
                } else {
                    Identifier::Indexed(
                        Symbol(name),
                        st.alloc_slice(&index.iter().map(|idx| idx.ast(st)).collect_vec()),
                    )
                };
                if parameters.is_empty() {
                    ast::Sort::Sort(ident)
                } else {
                    ast::Sort::Parametric(
                        ident,
                        st.alloc_slice(&parameters.iter().map(|param| param.ast()).collect_vec()),
                    )
                }
            }
        }
    }

    pub fn new_const(
        &self,
        st: &'st Storage,
        name: impl Into<String>,
    ) -> terms::Const<terms::Dynamic> {
        let name: &'static str = String::leak(name.into());
        terms::Const(
            name,
            terms::Dynamic::from_term_sort(
                STerm::new(
                    st,
                    ast::Term::Identifier(qual_ident(name, Some(self.ast()))),
                ),
                *self,
            ),
        )
    }
}
