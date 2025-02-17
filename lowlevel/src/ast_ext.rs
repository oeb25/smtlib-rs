use crate::{ast, lexicon};

impl<'st> From<&'st str> for lexicon::Symbol<'st> {
    fn from(s: &'st str) -> Self {
        lexicon::Symbol(s)
    }
}

impl<'st> ast::Identifier<'st> {
    pub const fn simple(s: &'st str) -> Self {
        ast::Identifier::Simple(lexicon::Symbol(s))
    }
    pub const fn indexed(s: &'st str, index: &'st [ast::Index<'st>]) -> Self {
        ast::Identifier::Indexed(lexicon::Symbol(s), index)
    }
}

impl<'st> ast::Sort<'st> {
    pub const fn new_simple(name: &'st str) -> Self {
        ast::Sort::Sort(ast::Identifier::simple(name))
    }
    pub const fn new_indexed(name: &'st str, index: &'st [ast::Index<'st>]) -> Self {
        ast::Sort::Sort(ast::Identifier::Indexed(lexicon::Symbol(name), index))
    }
    pub const fn new_simple_parametric(name: &'st str, parameters: &'st [ast::Sort<'st>]) -> Self {
        ast::Sort::Parametric(ast::Identifier::simple(name), parameters)
    }
    pub const fn new_indexed_parametric(
        name: &'st str,
        index: &'st [ast::Index<'st>],
        parameters: &'st [ast::Sort<'st>],
    ) -> Self {
        ast::Sort::Parametric(
            ast::Identifier::Indexed(lexicon::Symbol(name), index),
            parameters,
        )
    }
}
