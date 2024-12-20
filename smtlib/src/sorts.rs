use smtlib_lowlevel::{
    ast::{self, Identifier},
    lexicon::{Numeral, Symbol},
};

use crate::terms::{self, qual_ident};

pub struct SortTemplate {
    pub name: String,
    pub index: Vec<Index>,
    pub arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sort {
    pub name: String,
    pub index: Vec<Index>,
    pub parameters: Vec<Sort>,
}

impl std::fmt::Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.ast().fmt(f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Index {
    Numeral(usize),
    Symbol(String),
}

impl SortTemplate {
    pub fn instantiate(&self, parameters: Vec<Sort>) -> Result<Sort, crate::Error> {
        if self.arity != parameters.len() {
            return Err(todo!());
        }

        Ok(Sort {
            name: self.name.clone(),
            index: self.index.clone(),
            parameters,
        })
    }
}

impl Index {
    fn ast(&self) -> ast::Index {
        match self {
            Index::Numeral(n) => ast::Index::Numeral(Numeral(n.to_string())),
            Index::Symbol(s) => ast::Index::Symbol(Symbol(s.to_string())),
        }
    }
}

pub(crate) fn is_built_in_sort(name: &str) -> bool {
    match name {
        "Int" | "Bool" | "Real" => true,
        _ => false,
    }
}

impl Sort {
    pub fn new(name: impl Into<String>) -> Self {
        let mut name = name.into();
        Self {
            name,
            index: Vec::new(),
            parameters: Vec::new(),
        }
    }

    pub fn new_parametric(name: impl Into<String>, parameters: Vec<Sort>) -> Self {
        Self {
            name: name.into(),
            index: Vec::new(),
            parameters,
        }
    }

    pub fn new_indexed(name: impl Into<String>, index: Vec<Index>) -> Self {
        Self {
            name: name.into(),
            index,
            parameters: Vec::new(),
        }
    }

    pub fn ast(&self) -> ast::Sort {
        let ident = if self.index.is_empty() {
            Identifier::Simple(Symbol(self.name.to_string()))
        } else {
            Identifier::Indexed(
                Symbol(self.name.to_string()),
                self.index.iter().map(|idx| idx.ast()).collect(),
            )
        };
        if self.parameters.is_empty() {
            ast::Sort::Sort(ident)
        } else {
            ast::Sort::Parametric(
                ident,
                self.parameters.iter().map(|param| param.ast()).collect(),
            )
        }
    }

    pub fn new_const(&self, name: impl Into<String>) -> terms::Const<terms::Dynamic> {
        let name: &'static str = String::leak(name.into());
        terms::Const(
            name,
            terms::Dynamic::from_term_sort(
                ast::Term::Identifier(qual_ident(name.into(), Some(self.ast()))),
                self.clone(),
            ),
        )
    }
}
