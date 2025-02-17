#![doc = concat!("```ignore\n", include_str!("./Reals.smt2"), "```")]

use smtlib_lowlevel::{
    ast::{self, Term},
    Storage,
};

use crate::{
    impl_op,
    sorts::Sort,
    terms::{app, qual_ident, Const, Dynamic, IntoWithStorage, STerm, Sorted, StaticSorted},
    Bool,
};

/// A [`Real`] is a term containing a
/// [real](https://en.wikipedia.org/wiki/Real_number). You can [read more
/// here.](https://smtlib.cs.uiowa.edu/theories-Reals.shtml).
#[derive(Debug, Clone, Copy)]
pub struct Real<'st>(STerm<'st>);
impl<'st> From<Const<'st, Real<'st>>> for Real<'st> {
    fn from(c: Const<'st, Real<'st>>) -> Self {
        c.1
    }
}
impl<'st> IntoWithStorage<'st, Real<'st>> for Const<'st, Real<'st>> {
    fn into_with_storage(self, _st: &'st Storage) -> Real<'st> {
        self.1
    }
}
impl std::fmt::Display for Real<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.term().fmt(f)
    }
}

impl<'st> From<Real<'st>> for Dynamic<'st> {
    fn from(i: Real<'st>) -> Self {
        i.into_dynamic()
    }
}

impl<'st> From<Real<'st>> for STerm<'st> {
    fn from(i: Real<'st>) -> Self {
        i.0
    }
}
impl<'st> From<STerm<'st>> for Real<'st> {
    fn from(t: STerm<'st>) -> Self {
        Real(t)
    }
}
impl<'st> StaticSorted<'st> for Real<'st> {
    type Inner = Self;
    const AST_SORT: ast::Sort<'static> = ast::Sort::new_simple("Real");
    fn static_st(&self) -> &'st Storage {
        self.0.st()
    }
}
impl<'st> IntoWithStorage<'st, Real<'st>> for i64 {
    fn into_with_storage(self, st: &'st Storage) -> Real<'st> {
        (self as f64).into_with_storage(st)
    }
}
impl<'st> IntoWithStorage<'st, Real<'st>> for f64 {
    fn into_with_storage(self, st: &'st Storage) -> Real<'st> {
        let s = Term::Identifier(qual_ident(st.alloc_str(&format!("{:?}", self.abs())), None));
        let term = if self.is_sign_negative() {
            Term::Application(qual_ident("-", None), st.alloc_slice(&[st.alloc_term(s)]))
        } else {
            s
        };
        STerm::new(st, term).into()
    }
}
impl<'st> Real<'st> {
    /// Returns the sort of reals.
    pub fn sort() -> Sort<'st> {
        Self::AST_SORT.into()
    }
    fn binop<T: From<STerm<'st>>>(self, op: &'st str, other: Real<'st>) -> T {
        app(self.st(), op, (self.term(), other.term())).into()
    }
    /// Construct the term expressing `(> self other)`
    pub fn gt(self, other: impl Into<Self>) -> Bool<'st> {
        self.binop(">", other.into())
    }
    /// Construct the term expressing `(>= self other)`
    pub fn ge(self, other: impl Into<Self>) -> Bool<'st> {
        self.binop(">=", other.into())
    }
    /// Construct the term expressing `(< self other)`
    pub fn lt(self, other: impl Into<Self>) -> Bool<'st> {
        self.binop("<", other.into())
    }
    /// Construct the term expressing `(<= self other)`
    pub fn le(self, other: impl Into<Self>) -> Bool<'st> {
        self.binop("<=", other.into())
    }
    /// Construct the term expressing `(abs self)`
    pub fn abs(self) -> Real<'st> {
        app(self.st(), "abs", self.term()).into()
    }
}

impl std::ops::Neg for Real<'_> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        app(self.st(), "-", self.term()).into()
    }
}

impl_op!(Real<'st>, f64, Add, add, "+", AddAssign, add_assign, +);
impl_op!(Real<'st>, f64, Sub, sub, "-", SubAssign, sub_assign, -);
impl_op!(Real<'st>, f64, Mul, mul, "*", MulAssign, mul_assign, *);
impl_op!(Real<'st>, f64, Div, div, "div", DivAssign, div_assign, /);
