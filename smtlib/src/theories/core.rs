#![doc = concat!("```ignore\n", include_str!("./Core.smt2"), "```")]

use smtlib_lowlevel::{
    ast::{self, Term},
    Storage,
};

use crate::{
    impl_op,
    sorts::Sort,
    terms::{app, qual_ident, Const, Dynamic, IntoWithStorage, STerm, Sorted, StaticSorted},
};

/// A [`Bool`] is a term containing a
/// [boolean](https://en.wikipedia.org/wiki/Boolean_data_type). You can [read more
/// here.](https://smtlib.cs.uiowa.edu/theories-Core.shtml).
#[derive(Clone, Copy)]
pub struct Bool<'st>(STerm<'st>);

impl<'st> Bool<'st> {
    /// Construct a new bool.
    pub fn new(st: &'st Storage, value: bool) -> Bool<'st> {
        value.into_with_storage(st)
    }
}

impl std::fmt::Debug for Bool<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'st> From<Const<'st, Bool<'st>>> for Bool<'st> {
    fn from(c: Const<'st, Bool<'st>>) -> Self {
        c.1
    }
}
impl<'st> IntoWithStorage<'st, Bool<'st>> for Const<'st, Bool<'st>> {
    fn into_with_storage(self, _st: &'st Storage) -> Bool<'st> {
        self.1
    }
}
impl std::fmt::Display for Bool<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.term().fmt(f)
    }
}
impl<'st> From<Bool<'st>> for Dynamic<'st> {
    fn from(b: Bool<'st>) -> Self {
        b.into_dynamic()
    }
}
impl<'st> IntoWithStorage<'st, Bool<'st>> for bool {
    fn into_with_storage(self, st: &'st Storage) -> Bool<'st> {
        let s = match self {
            true => "true",
            false => "false",
        };

        STerm::new(st, Term::Identifier(qual_ident(s, None))).into()
    }
}
impl<'st> From<Bool<'st>> for STerm<'st> {
    fn from(b: Bool<'st>) -> Self {
        b.0
    }
}
impl<'st> From<STerm<'st>> for Bool<'st> {
    fn from(t: STerm<'st>) -> Self {
        Bool(t)
    }
}
impl<'st> From<(STerm<'st>, Sort<'st>)> for Bool<'st> {
    fn from((t, _): (STerm<'st>, Sort<'st>)) -> Self {
        t.into()
    }
}
impl<'st> StaticSorted<'st> for Bool<'st> {
    type Inner = Self;
    const AST_SORT: ast::Sort<'static> = ast::Sort::new_simple("Bool");
    fn static_st(&self) -> &'st Storage {
        self.sterm().st()
    }
}
impl<'st> Bool<'st> {
    /// Returns the sort of bools.
    pub fn sort() -> Sort<'st> {
        Self::AST_SORT.into()
    }
    fn binop(self, op: &'st str, other: Bool<'st>) -> Self {
        app(self.st(), op, (self.term(), other.term())).into()
    }
    /// Construct the term expressing `(==> self other)`.
    ///
    /// The value of the returned boolean is true if:
    /// - `self` is false
    /// - or `other` is true
    pub fn implies(self, other: Bool<'st>) -> Bool<'st> {
        self.binop("=>", other)
    }
    /// Construct the term expressing `(ite self then otherwise)`.
    ///
    /// This is similar to the [ternary condition
    /// operator](https://en.wikipedia.org/wiki/Ternary_conditional_operator),
    /// and an if statement:
    /// - **C-style notation:** `self ? then : otherwise`
    /// - **Rust notation:**  `if self { then } else { otherwise }`
    pub fn ite<T: Sorted<'st> + From<(STerm<'st>, Sort<'st>)>>(self, then: T, otherwise: T) -> T {
        let sort = then.sort();
        let term = app(
            self.st(),
            "ite",
            (self.term(), then.term(), otherwise.term()),
        );
        let dyn_term = Dynamic::from_term_sort(term, sort);
        T::from_dynamic(dyn_term)
    }
}

impl_op!(Bool<'st>, bool, BitAnd, bitand, "and", BitAndAssign, bitand_assign, &);
impl_op!(Bool<'st>, bool, BitOr,  bitor,  "or", BitOrAssign,  bitor_assign,  |);
impl_op!(Bool<'st>, bool, BitXor, bitxor, "xor",  BitXorAssign, bitxor_assign, ^);

impl<'st> std::ops::Not for Bool<'st> {
    type Output = Bool<'st>;

    fn not(self) -> Self::Output {
        app(self.st(), "not", self.term()).into()
    }
}

/// Construct the term expressing `(and ...terms)` representing the conjunction
/// of all of the terms. That is to say, the result is true iff all terms in
/// `terms` is true.
pub fn and<'st, const N: usize>(st: &'st Storage, terms: [Bool<'st>; N]) -> Bool<'st> {
    app(st, "and", terms.map(Sorted::term)).into()
}
/// Construct the term expressing `(or ...terms)` representing the disjunction
/// of all of the terms. That is to say, the result is true iff any of the terms
/// in `terms` is true.
pub fn or<'st, const N: usize>(st: &'st Storage, terms: [Bool<'st>; N]) -> Bool<'st> {
    app(st, "or", terms.map(Sorted::term)).into()
}
/// Construct the term expressing `(xor ...terms)`.
pub fn xor<'st, const N: usize>(st: &'st Storage, terms: [Bool<'st>; N]) -> Bool<'st> {
    app(st, "xor", terms.map(Sorted::term)).into()
}

/// Construct the term expressing `(equal terms)` representing that all of the
/// terms in `terms` are equal.
pub fn equal<'st, T, const N: usize>(st: &'st Storage, terms: [T; N]) -> Bool<'st>
where
    T: Into<STerm<'st>>,
{
    app(st, "=", terms.map(Into::into).map(STerm::term)).into()
}
/// Construct the term expressing `(distinct terms)` representing that all of
/// the terms in `terms` are distinct (or not-equal).
pub fn distinct<'st, T, const N: usize>(st: &'st Storage, terms: [T; N]) -> Bool<'st>
where
    T: Into<STerm<'st>>,
{
    app(st, "distinct", terms.map(Into::into).map(STerm::term)).into()
}
