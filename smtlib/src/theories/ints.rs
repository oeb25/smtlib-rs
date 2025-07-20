#![doc = concat!("```ignore\n", include_str!("./Ints.smt2"), "```")]

use smtlib_lowlevel::{
    ast::{self, Identifier, QualIdentifier, SpecConstant, Term},
    lexicon::{Numeral, Symbol},
    Storage,
};

use crate::{
    impl_op,
    sorts::Sort,
    terms::{app, Const, Dynamic, IntoWithStorage, STerm, Sorted, StaticSorted},
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
    const AST_SORT: ast::Sort<'static> = ast::Sort::new_simple("Int");

    fn static_st(&self) -> &'st Storage {
        self.0.st()
    }
}
impl<'st> IntoWithStorage<'st, Int<'st>> for i128 {
    fn into_with_storage(self, st: &'st Storage) -> Int<'st> {
        let term = if self < 0 {
            app(
                st,
                "-",
                Term::SpecConstant(SpecConstant::Numeral(Numeral::from_u128(
                    self.unsigned_abs() as _,
                ))),
            )
        } else {
            STerm::new(
                st,
                Term::SpecConstant(SpecConstant::Numeral(Numeral::from_u128(self as _))),
            )
        };
        term.into()
    }
}
/// Error returned when trying to convert an [`Int`] to a primitive type.
#[derive(Debug, thiserror::Error, PartialEq, Eq, PartialOrd, Ord)]
pub enum TryFromError {
    #[error("numeral was a string. this happens when the numeral is too large to fit into u128")]
    /// The numeral is too large to fit into a u128.
    NumeralWasString,
    #[error("out of range {}", if *neg { format!("-{abs}") } else { abs.to_string() })]
    /// Too large to fit into the target type.
    OutOfRange {
        /// The number is negative.
        neg: bool,
        /// The absolute value of the number.
        abs: u128,
    },
    #[error("numeral was not a spec constant or a negation of a numeral")]
    /// The term was not a numeral or a negation of a numeral.
    NotANumeral,
}
impl<'st> TryFrom<Int<'st>> for i128 {
    type Error = TryFromError;
    fn try_from(i: Int<'st>) -> Result<Self, Self::Error> {
        match i.term() {
            Term::SpecConstant(SpecConstant::Numeral(c)) => {
                let n = c.into_u128().map_err(|_| TryFromError::NumeralWasString)?;
                n.try_into()
                    .map_err(|_| TryFromError::OutOfRange { abs: n, neg: false })
            }
            Term::Application(
                QualIdentifier::Identifier(Identifier::Simple(Symbol("-"))),
                [Term::SpecConstant(SpecConstant::Numeral(c))],
            ) => {
                let n = c.into_u128().map_err(|_| TryFromError::NumeralWasString)?;
                if n == i128::MIN as u128 {
                    // This is a special case, as i128::MIN cannot be
                    // represented as a positive i128.
                    return Ok(i128::MIN);
                }
                n.try_into()
                    .map_err(|_| TryFromError::OutOfRange { abs: n, neg: true })
                    .map(|n: i128| -n)
            }
            _ => Err(TryFromError::NotANumeral),
        }
    }
}
impl<'st> IntoWithStorage<'st, Int<'st>> for u128 {
    fn into_with_storage(self, st: &'st Storage) -> Int<'st> {
        STerm::new(
            st,
            Term::SpecConstant(SpecConstant::Numeral(Numeral::from_u128(self as _))),
        )
        .into()
    }
}
impl<'st> TryFrom<Int<'st>> for u128 {
    type Error = TryFromError;
    fn try_from(i: Int<'st>) -> Result<Self, Self::Error> {
        match i.term() {
            Term::SpecConstant(SpecConstant::Numeral(c)) => {
                c.into_u128().map_err(|_| TryFromError::NumeralWasString)
            }
            _ => Err(TryFromError::NotANumeral),
        }
    }
}
macro_rules! impl_int_conv {
    (from $s:ty, into $t:ty) => {
        impl<'st> IntoWithStorage<'st, Int<'st>> for $t {
            fn into_with_storage(self, st: &'st Storage) -> Int<'st> {
                IntoWithStorage::into_with_storage(self as $s, st)
            }
        }
        impl<'st> TryFrom<Int<'st>> for $t {
            type Error = TryFromError;
            fn try_from(i: Int<'st>) -> Result<Self, Self::Error> {
                let n = <$s>::try_from(i)?;
                n.try_into().map_err(|_| TryFromError::OutOfRange {
                    abs: n as u128,
                    #[allow(unused_comparisons)]
                    neg: n < 0,
                })
            }
        }
    };
}
impl_int_conv!(from i128, into i8);
impl_int_conv!(from i128, into i16);
impl_int_conv!(from i128, into i32);
impl_int_conv!(from i128, into i64);
impl_int_conv!(from i128, into isize);
impl_int_conv!(from u128, into u8);
impl_int_conv!(from u128, into u16);
impl_int_conv!(from u128, into u32);
impl_int_conv!(from u128, into u64);
impl_int_conv!(from u128, into usize);

impl<'st> Int<'st> {
    /// Returns the sort of ints.
    pub fn sort() -> Sort<'st> {
        Self::AST_SORT.into()
    }
    /// Construct a new integer.
    pub fn new(st: &'st Storage, value: impl IntoWithStorage<'st, Int<'st>>) -> Int<'st> {
        value.into_with_storage(st)
    }
    fn binop<T: From<STerm<'st>>>(self, op: &'st str, other: Int<'st>) -> T {
        app(self.static_st(), op, (self.term(), other.term())).into()
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
        app(self.st(), "abs", self.term()).into()
    }
}

impl std::ops::Neg for Int<'_> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        app(self.st(), "-", self.term()).into()
    }
}

impl_op!(Int<'st>, i64, Add, add, "+", AddAssign, add_assign, +);
impl_op!(Int<'st>, i64, Sub, sub, "-", SubAssign, sub_assign, -);
impl_op!(Int<'st>, i64, Mul, mul, "*", MulAssign, mul_assign, *);
impl_op!(Int<'st>, i64, Div, div, "div", DivAssign, div_assign, /);
impl_op!(Int<'st>, i64, Rem, rem, "rem", RemAssign, rem_assign, %);
impl_op!(Int<'st>, i64, Shl, shl, "hsl", ShlAssign, shl_assign, <<);
impl_op!(Int<'st>, i64, Shr, shr, "hsr", ShrAssign, shr_assign, >>);
