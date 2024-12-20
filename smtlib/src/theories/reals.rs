#![doc = concat!("```ignore\n", include_str!("./Reals.smt2"), "```")]

use smtlib_lowlevel::ast::Term;

use crate::{
    Bool, impl_op,
    sorts::Sort,
    terms::{Const, Dynamic, Sorted, StaticSorted, fun, qual_ident},
};

/// A [`Real`] is a term containing a
/// [real](https://en.wikipedia.org/wiki/Real_number). You can [read more
/// here.](https://smtlib.cs.uiowa.edu/theories-Reals.shtml).
#[derive(Debug, Clone, Copy)]
pub struct Real(&'static Term);
impl From<Const<Real>> for Real {
    fn from(c: Const<Real>) -> Self {
        c.1
    }
}
impl std::fmt::Display for Real {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Term::from(*self).fmt(f)
    }
}

impl From<Real> for Dynamic {
    fn from(i: Real) -> Self {
        i.into_dynamic()
    }
}

impl From<Real> for Term {
    fn from(i: Real) -> Self {
        i.0.clone()
    }
}
impl From<Term> for Real {
    fn from(t: Term) -> Self {
        Real(Box::leak(Box::new(t)))
    }
}
impl StaticSorted for Real {
    type Inner = Self;

    fn static_sort() -> Sort {
        Sort::new("Real")
    }
}
impl From<i64> for Real {
    fn from(i: i64) -> Self {
        (i as f64).into()
    }
}
impl From<f64> for Real {
    fn from(i: f64) -> Self {
        let s = Term::Identifier(qual_ident(format!("{:?}", i.abs()), None));
        if i.is_sign_negative() {
            Term::Application(qual_ident("-".to_string(), None), vec![s]).into()
        } else {
            s.into()
        }
    }
}
impl Real {
    pub fn sort() -> Sort {
        Self::static_sort()
    }

    fn binop<T: From<Term>>(self, op: &str, other: Real) -> T {
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

    /// Construct the term expressing `(abs self)`
    pub fn abs(self) -> Real {
        fun("abs", vec![self.into()]).into()
    }

    /// Construct the term expressing floor division of two terms
    pub fn floor_div<R>(self, rhs: R) -> Self
    where
        R: Into<Real>,
    {
        self.binop("div", rhs.into())
    }
}

impl std::ops::Neg for Real {
    type Output = Self;

    fn neg(self) -> Self::Output {
        fun("-", vec![self.into()]).into()
    }
}

impl_op!(Real, f64, Add, add, "+", AddAssign, add_assign, +);
impl_op!(Real, f64, Sub, sub, "-", SubAssign, sub_assign, -);
impl_op!(Real, f64, Mul, mul, "*", MulAssign, mul_assign, *);
impl_op!(Real, f64, Div, div, "/", DivAssign, div_assign, /);
