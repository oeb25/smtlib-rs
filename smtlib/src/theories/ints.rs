#![doc = concat!("```ignore\n", include_str!("./Ints.smt2"), "```")]

use smtlib_lowlevel::{
    ast::{SpecConstant, Term},
    lexicon::Numeral,
    Storage,
};

use crate::{
    impl_op,
    sorts::Sort,
    terms::{fun_vec, Const, Dynamic, IntoWithStorage, STerm, Sorted, StaticSorted},
    Bool,
};

/// A [`Int`] is a term containing a
/// [integer](https://en.wikipedia.org/wiki/Integer). You can [read more
/// here.](https://smtlib.cs.uiowa.edu/theories-Ints.shtml).
#[derive(Debug, Clone, Copy)]
pub struct Int<'st>(STerm<'st>);
impl<'st> From<Const<'st, Int<'st>>> for Int<'st> {
    fn from(c: Const<'st, Int<'st>>) -> Self {
        c.1
    }
}
impl<'st> IntoWithStorage<'st, Int<'st>> for Const<'st, Int<'st>> {
    fn into_with_storage(self, _st: &'st Storage) -> Int<'st> {
        self.1
    }
}
impl std::fmt::Display for Int<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        STerm::from(*self).term().fmt(f)
    }
}

impl<'st> From<Int<'st>> for Dynamic<'st> {
    fn from(i: Int<'st>) -> Self {
        i.into_dynamic()
    }
}

impl<'st> From<Int<'st>> for STerm<'st> {
    fn from(i: Int<'st>) -> Self {
        i.0
    }
}
impl<'st> From<STerm<'st>> for Int<'st> {
    fn from(t: STerm<'st>) -> Self {
        Int(t)
    }
}
impl<'st> From<(STerm<'st>, Sort<'st>)> for Int<'st> {
    fn from((t, _): (STerm<'st>, Sort<'st>)) -> Self {
        t.into()
    }
}
impl<'st> StaticSorted<'st> for Int<'st> {
    type Inner = Self;
    const SORT: Sort<'st> = Sort::new_static("Int", &[]);

    fn static_st(&self) -> &'st Storage {
        self.0.st()
    }
}
impl<'st> IntoWithStorage<'st, Int<'st>> for i64 {
    fn into_with_storage(self, st: &'st Storage) -> Int<'st> {
        let term = if self < 0 {
            fun_vec(
                st,
                "-",
                [st.alloc_term(Term::SpecConstant(SpecConstant::Numeral(
                    Numeral::from_usize(self.unsigned_abs() as _),
                )))]
                .to_vec(),
            )
        } else {
            STerm::new(
                st,
                Term::SpecConstant(SpecConstant::Numeral(Numeral::from_usize(self as _))),
            )
        };
        term.into()
    }
}
impl<'st> Int<'st> {
    /// Returns the sort of ints.
    pub fn sort() -> Sort<'st> {
        Self::SORT
    }
    /// Construct a new integer.
    pub fn new(st: &'st Storage, value: impl IntoWithStorage<'st, Int<'st>>) -> Int<'st> {
        value.into_with_storage(st)
    }
    fn binop<T: From<STerm<'st>>>(self, op: &str, other: Int<'st>) -> T {
        fun_vec(
            self.static_st(),
            self.st().alloc_str(op),
            [self.term(), other.term()].to_vec(),
        )
        .into()
    }
    /// Construct the term expressing `(> self other)`
    pub fn gt(self, other: impl IntoWithStorage<'st, Self>) -> Bool<'st> {
        self.binop(">", other.into_with_storage(self.st()))
    }
    /// Construct the term expressing `(>= self other)`
    pub fn ge(self, other: impl IntoWithStorage<'st, Self>) -> Bool<'st> {
        self.binop(">=", other.into_with_storage(self.st()))
    }
    /// Construct the term expressing `(< self other)`
    pub fn lt(self, other: impl IntoWithStorage<'st, Self>) -> Bool<'st> {
        self.binop("<", other.into_with_storage(self.st()))
    }
    /// Construct the term expressing `(<= self other)`
    pub fn le(self, other: impl IntoWithStorage<'st, Self>) -> Bool<'st> {
        self.binop("<=", other.into_with_storage(self.st()))
    }
    // TODO: This seems to not be supported by z3?
    /// Construct the term expressing `(abs self)`
    pub fn abs(self) -> Int<'st> {
        fun_vec(self.st(), "abs", vec![self.term()]).into()
    }
}

impl std::ops::Neg for Int<'_> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        fun_vec(self.st(), "-", vec![self.term()]).into()
    }
}

impl_op!(Int<'st>, i64, Add, add, "+", AddAssign, add_assign, +);
impl_op!(Int<'st>, i64, Sub, sub, "-", SubAssign, sub_assign, -);
impl_op!(Int<'st>, i64, Mul, mul, "*", MulAssign, mul_assign, *);
impl_op!(Int<'st>, i64, Div, div, "div", DivAssign, div_assign, /);
impl_op!(Int<'st>, i64, Rem, rem, "rem", RemAssign, rem_assign, %);
impl_op!(Int<'st>, i64, Shl, shl, "hsl", ShlAssign, shl_assign, <<);
impl_op!(Int<'st>, i64, Shr, shr, "hsr", ShrAssign, shr_assign, >>);
