#![doc = concat!("```ignore\n", include_str!("./Reals.smt2"), "```")]

use smtlib_lowlevel::{ast::Term, Storage};

use crate::{
    impl_op,
    sorts::Sort,
    terms::{fun_vec, qual_ident, Const, Dynamic, IntoWithStorage, STerm, Sorted, StaticSorted},
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
    fn static_sort() -> Sort<'st> {
        Sort::new_static("Real", &[])
    }
    fn static_st(&self) -> &'st smtlib_lowlevel::Storage {
        self.0.st()
    }
}
// impl<'st> From<i64> for Real<'st> {
//     fn from(i: i64) -> Self {
//         (i as f64).into()
//     }
// }
// impl<'st> From<f64> for Real<'st> {
//     fn from(i: f64) -> Self {
//         let s = Term::Identifier(qual_ident(format!("{:?}", i.abs()), None));
//         if i.is_sign_negative() {
//             Term::Application(qual_ident("-".to_string(), None), vec![s]).into()
//         } else {
//             s.into()
//         }
//     }
// }
impl<'st> IntoWithStorage<'st, Real<'st>> for f64 {
    fn into_with_storage(self, st: &'st smtlib_lowlevel::Storage) -> Real<'st> {
        let s = Term::Identifier(qual_ident(st.alloc_str(&format!("{:?}", self.abs())), None));
        let term = if self.is_sign_negative() {
            Term::Application(qual_ident("-", None), st.alloc_slice(&[st.alloc_term(s)]))
        } else {
            s
        };
        STerm::new(st, term).into()
    }

    // fn from(i: f64) -> Self {
    // }
}
impl<'st> Real<'st> {
    pub fn sort() -> Sort<'st> {
        Self::static_sort()
    }
    fn binop<T: From<STerm<'st>>>(self, op: &str, other: Real<'st>) -> T {
        fun_vec(
            self.st(),
            self.st().alloc_str(op),
            [self.term(), other.term()].to_vec(),
        )
        .into()
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
        fun_vec(self.st(), "abs", vec![self.term()]).into()
    }
}

impl std::ops::Neg for Real<'_> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        fun_vec(self.st(), "-", vec![self.term()]).into()
    }
}

impl_op!(Real<'st>, f64, Add, add, "+", AddAssign, add_assign, +);
impl_op!(Real<'st>, f64, Sub, sub, "-", SubAssign, sub_assign, -);
impl_op!(Real<'st>, f64, Mul, mul, "*", MulAssign, mul_assign, *);
impl_op!(Real<'st>, f64, Div, div, "div", DivAssign, div_assign, /);
