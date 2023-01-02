#![doc = concat!("```ignore\n", include_str!("./Core.smt2"), "```")]

use smtlib_lowlevel::{
    ast::{self, Identifier, Term},
    lexicon::Symbol,
};

use crate::{
    impl_op,
    terms::{fun, qual_ident, Const, Dynamic, Sort},
};

#[derive(Clone, Copy)]
pub struct Bool(BoolImpl);

impl std::fmt::Debug for Bool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Debug, Clone, Copy)]
enum BoolImpl {
    #[allow(unused)]
    Const(&'static str),
    Term(&'static Term),
}
impl From<Const<Bool>> for Bool {
    fn from(c: Const<Bool>) -> Self {
        c.1
    }
}
impl std::fmt::Display for Bool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Term::from(*self).fmt(f)
    }
}
impl From<Bool> for Dynamic {
    fn from(b: Bool) -> Self {
        Term::from(b).into()
    }
}
impl From<bool> for Bool {
    fn from(b: bool) -> Self {
        let s = match b {
            true => "true",
            false => "false",
        };

        Term::Identifier(qual_ident(s.into(), None)).into()
    }
}
impl From<Bool> for Term {
    fn from(b: Bool) -> Self {
        match b.0 {
            BoolImpl::Const(name) => Term::Identifier(qual_ident(name.into(), None)),
            BoolImpl::Term(t) => t.clone(),
        }
    }
}
impl From<Term> for Bool {
    fn from(t: Term) -> Self {
        Bool(BoolImpl::Term(Box::leak(Box::new(t))))
    }
}
impl Sort for Bool {
    type Inner = Self;
    fn sort() -> ast::Sort {
        ast::Sort::Sort(Identifier::Simple(Symbol("Bool".into())))
    }
}
impl Bool {
    fn binop(self, op: &str, other: Bool) -> Self {
        fun(op, vec![self.into(), other.into()]).into()
    }
    pub fn implies(self, other: Bool) -> Bool {
        self.binop("=>", other)
    }
    pub fn ite(self, then: Bool, otherwise: Bool) -> Bool {
        fun("ite", vec![self.into(), then.into(), otherwise.into()]).into()
    }
}

impl_op!(Bool, bool, BitAnd, bitand, "and", BitAndAssign, bitand_assign, &);
impl_op!(Bool, bool, BitOr,  bitor,  "or", BitOrAssign,  bitor_assign,  |);
impl_op!(Bool, bool, BitXor, bitxor, "xor",  BitXorAssign, bitxor_assign, ^);

impl std::ops::Not for Bool {
    type Output = Bool;

    fn not(self) -> Self::Output {
        fun("not", vec![self.into()]).into()
    }
}

pub fn and<const N: usize>(terms: [Bool; N]) -> Bool {
    fun("and", terms.map(Into::into).to_vec()).into()
}
pub fn or<const N: usize>(terms: [Bool; N]) -> Bool {
    fun("or", terms.map(Into::into).to_vec()).into()
}
pub fn xor<const N: usize>(terms: [Bool; N]) -> Bool {
    fun("xor", terms.map(Into::into).to_vec()).into()
}

pub fn equal<T, const N: usize>(terms: [T; N]) -> Bool
where
    T: Into<ast::Term>,
{
    fun("equal", terms.map(Into::into).to_vec()).into()
}
pub fn distinct<T, const N: usize>(terms: [T; N]) -> Bool
where
    T: Into<ast::Term>,
{
    fun("distinct", terms.map(Into::into).to_vec()).into()
}
