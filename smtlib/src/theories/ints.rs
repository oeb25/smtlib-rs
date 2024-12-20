#![doc = concat!("```ignore\n", include_str!("./Ints.smt2"), "```")]

use smtlib_lowlevel::{ast::Term, lexicon::Numeral};

use crate::{
    Bool, impl_op,
    sorts::Sort,
    terms::{Const, Dynamic, Sorted, StaticSorted, fun, qual_ident},
};

/// A [`Int`] is a term containing a
/// [integer](https://en.wikipedia.org/wiki/Integer). You can [read more
/// here.](https://smtlib.cs.uiowa.edu/theories-Ints.shtml).
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
        i.into_dynamic()
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
impl From<(Term, Sort)> for Int {
    fn from((t, _): (Term, Sort)) -> Self {
        t.into()
    }
}
impl StaticSorted for Int {
    type Inner = Self;

    fn static_sort() -> Sort {
        Sort::new("Int")
    }
}
impl From<i64> for Int {
    fn from(i: i64) -> Self {
        Term::SpecConstant(smtlib_lowlevel::ast::SpecConstant::Numeral(Numeral(
            i.to_string(),
        )))
        .into()
    }
}
impl Int {
    pub fn sort() -> Sort {
        Self::static_sort()
    }

    fn binop<T: From<Term>>(self, op: &str, other: Int) -> T {
        fun(op, vec![self.into(), other.into()]).into()
    }

    /// Construct the term expressing `(> self other)`
    pub fn gt(self, other: impl Into<Self>) -> Bool {
        self.binop(">", other.into())
    }

    /// Construct the term expressing `(>= self other)`
    pub fn ge(self, other: impl Into<Self>) -> Bool {
        self.binop(">=", other.into())
    }

    /// Construct the term expressing `(< self other)`
    pub fn lt(self, other: impl Into<Self>) -> Bool {
        self.binop("<", other.into())
    }

    /// Construct the term expressing `(<= self other)`
    pub fn le(self, other: impl Into<Self>) -> Bool {
        self.binop("<=", other.into())
    }

    // TODO: This seems to not be supported by z3?
    /// Construct the term expressing `(abs self)`
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
impl_op!(Int, i64, Rem, rem, "rem", RemAssign, rem_assign, %);
impl_op!(Int, i64, Shl, shl, "hsl", ShlAssign, shl_assign, <<);
impl_op!(Int, i64, Shr, shr, "hsr", ShrAssign, shr_assign, >>);
