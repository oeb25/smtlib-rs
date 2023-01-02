#![doc = concat!("```ignore\n", include_str!("./Ints.smt2"), "```")]

use smtlib_lowlevel::{
    ast::{self, Identifier, Term},
    lexicon::Symbol,
};

use crate::{
    impl_op,
    terms::{fun, qual_ident, Const, Dynamic, Sort},
    Bool,
};

#[derive(Debug, Clone, Copy)]
pub struct Int(&'static Term);
impl From<Const<Int>> for Int {
    fn from(c: Const<Int>) -> Self {
        c.1
    }
}
impl std::fmt::Display for Int {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Term::from(*self).fmt(f)
    }
}

impl From<Int> for Dynamic {
    fn from(i: Int) -> Self {
        Term::from(i).into()
    }
}

impl From<Int> for Term {
    fn from(i: Int) -> Self {
        i.0.clone()
    }
}
impl From<Term> for Int {
    fn from(t: Term) -> Self {
        Int(Box::leak(Box::new(t)))
    }
}
impl Sort for Int {
    type Inner = Self;
    fn sort() -> ast::Sort {
        ast::Sort::Sort(Identifier::Simple(Symbol("Int".into())))
    }
}
impl From<i64> for Int {
    fn from(i: i64) -> Self {
        Term::Identifier(qual_ident(i.to_string(), None)).into()
    }
}
impl Int {
    fn binop<T: From<Term>>(self, op: &str, other: Int) -> T {
        fun(op, vec![self.into(), other.into()]).into()
    }
    pub fn gt(self, other: impl Into<Self>) -> Bool {
        self.binop(">", other.into())
    }
    pub fn ge(self, other: impl Into<Self>) -> Bool {
        self.binop(">=", other.into())
    }
    pub fn lt(self, other: impl Into<Self>) -> Bool {
        self.binop("<", other.into())
    }
    pub fn le(self, other: impl Into<Self>) -> Bool {
        self.binop("<=", other.into())
    }
    // TODO: This seems to not be supported by z3?
    pub fn abs(self) -> Int {
        fun("abs", vec![self.into()]).into()
    }
}

impl std::ops::Neg for Int {
    type Output = Self;
    fn neg(self) -> Self::Output {
        fun("-", vec![self.into()]).into()
    }
}

impl_op!(Int, i64, Add, add, "+", AddAssign, add_assign, +);
impl_op!(Int, i64, Sub, sub, "-", SubAssign, sub_assign, -);
impl_op!(Int, i64, Mul, mul, "*", MulAssign, mul_assign, *);
impl_op!(Int, i64, Div, div, "div", DivAssign, div_assign, /);
