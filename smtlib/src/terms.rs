//! Terms are the building blocks for constructing the mathematical expressions
//! used in assertions with [`Solver`](crate::Solver).
//!
//! They are a statically-typed and ergonomic layer on top of
//! [`smtlib_lowlevel::ast::Term`], which provides a more _Rust-like_ API.

use std::marker::PhantomData;

use itertools::Itertools;
use smtlib_lowlevel::{
    ast::{self, Attribute, AttributeValue, Identifier, QualIdentifier, SortedVar, Term},
    lexicon::{Keyword, Symbol},
    Storage,
};

use crate::{sorts::Sort, Bool};

/// Construct a `STerm` with the presence of `Storage`
pub trait IntoSTerm {
    /// Construct a `STerm` with the presence of `Storage`
    fn into_sterm(self, st: &'_ Storage) -> STerm<'_>;
}

/// Construct a `STerm` with the presence of `Storage`
pub trait IntoWithStorage<'st, T> {
    /// Construct a `STerm` with the presence of `Storage`
    fn into_with_storage(self, st: &'st Storage) -> T;
}

impl<'st, T> IntoWithStorage<'st, T> for T {
    fn into_with_storage(self, _st: &'st Storage) -> T {
        self
    }
}

impl<'st> IntoWithStorage<'st, &'st Term<'st>> for Term<'st> {
    fn into_with_storage(self, st: &'st Storage) -> &'st Term<'st> {
        st.alloc_term(self)
    }
}

/// A smtlib term with its associated storage.
///
/// This is a wrapper around a [`Term`] which also carries a pointer to its
/// [`Storage`]. Having a pointer to the storage allows new terms to be created
/// more ergonomically without passing around the storage.
#[derive(Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct STerm<'st> {
    #[cfg_attr(feature = "serde", serde(skip))]
    st: &'st Storage,
    term: &'st Term<'st>,
}

impl std::fmt::Debug for STerm<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("STerm")
            .field("st", &"Storage { .. }")
            .field("term", &self.term)
            .finish()
    }
}
impl<'st> STerm<'st> {
    /// Construct a new [`STerm`] with the given term in the given [`Storage`].
    pub fn new(st: &'st Storage, term: Term<'st>) -> Self {
        Self {
            st,
            term: st.alloc_term(term),
        }
    }
    /// Construct a new [`STerm`] with the given an already allocated term.
    pub fn new_from_ref(st: &'st Storage, term: &'st Term<'st>) -> Self {
        Self { st, term }
    }
    /// The [`Storage`] associated with the term.
    pub fn st(self) -> &'st Storage {
        self.st
    }
    /// The [`Term`] associated with the term.
    pub fn term(self) -> &'st Term<'st> {
        self.term
    }
}
impl std::fmt::Display for STerm<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.term().fmt(f)
    }
}
impl<'st> From<STerm<'st>> for &'st Term<'st> {
    fn from(sterm: STerm<'st>) -> Self {
        sterm.term
    }
}

pub(crate) fn app<'st>(
    st: &'st Storage,
    name: &'st str,
    args: impl ApplicationArgs<'st>,
) -> STerm<'st> {
    STerm::new(
        st,
        Term::Application(qual_ident(name, None), args.into_args(st)),
    )
}

pub(crate) trait ApplicationArgs<'st> {
    fn into_args(self, st: &'st Storage) -> &'st [&'st Term<'st>];
}

impl<'st, A: IntoWithStorage<'st, &'st Term<'st>>> ApplicationArgs<'st> for A {
    fn into_args(self, st: &'st Storage) -> &'st [&'st Term<'st>] {
        st.alloc_slice(&[self.into_with_storage(st)])
    }
}
impl<'st, A: IntoWithStorage<'st, &'st Term<'st>>, B: IntoWithStorage<'st, &'st Term<'st>>>
    ApplicationArgs<'st> for (A, B)
{
    fn into_args(self, st: &'st Storage) -> &'st [&'st Term<'st>] {
        st.alloc_slice(&[self.0.into_with_storage(st), self.1.into_with_storage(st)])
    }
}
impl<
        'st,
        A: IntoWithStorage<'st, &'st Term<'st>>,
        B: IntoWithStorage<'st, &'st Term<'st>>,
        C: IntoWithStorage<'st, &'st Term<'st>>,
    > ApplicationArgs<'st> for (A, B, C)
{
    fn into_args(self, st: &'st Storage) -> &'st [&'st Term<'st>] {
        st.alloc_slice(&[
            self.0.into_with_storage(st),
            self.1.into_with_storage(st),
            self.2.into_with_storage(st),
        ])
    }
}
impl<'st, A: IntoWithStorage<'st, &'st Term<'st>>, const N: usize> ApplicationArgs<'st> for [A; N] {
    fn into_args(self, st: &'st Storage) -> &'st [&'st Term<'st>] {
        st.alloc_slice(&self.map(|a| a.into_with_storage(st)))
    }
}

pub(crate) fn qual_ident<'st>(s: &'st str, sort: Option<ast::Sort<'st>>) -> QualIdentifier<'st> {
    if let Some(sort) = sort {
        QualIdentifier::Sorted(Identifier::Simple(Symbol(s)), sort)
    } else {
        QualIdentifier::Identifier(Identifier::Simple(Symbol(s)))
    }
}

/// This struct wraps specific instances of other terms to indicate that they
/// are constant. Constants are named terms whose value can be extracted from a
/// model using [`Model::eval`](crate::Model::eval).
///
/// To construct a `Const<'st, T>` call [`T::new_const`](Sort::new_const) where
/// `T` implements [`Sort`].
#[derive(Debug, Clone, Copy)]
pub struct Const<'st, T>(pub(crate) &'st str, pub(crate) T);

impl<T> Const<'_, T> {
    /// The name of the constant
    pub fn name(&self) -> &str {
        self.0
    }
}
impl<T> std::ops::Deref for Const<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.1
    }
}

/// This type wraps terms loosing all static type information. It is particular
/// useful when constructing terms dynamically.
#[derive(Debug, Clone, Copy)]
pub struct Dynamic<'st>(STerm<'st>, Sort<'st>);
impl std::fmt::Display for Dynamic<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        STerm::from(*self).term.fmt(f)
    }
}

/// A trait for statically typing STM-LIB terms.
///
/// Refer to the [`Sorted`] trait for a more general version of this trait.
pub trait StaticSorted<'st>: Into<STerm<'st>> + From<STerm<'st>> {
    /// The inner type of the term. This is used for [`Const<'st, T>`](Const)
    /// where the inner type is `T`.
    type Inner: StaticSorted<'st>;
    /// The sort of this sort.
    #[allow(clippy::declare_interior_mutable_const)]
    const AST_SORT: ast::Sort<'static>;
    /// The sort of this sort.
    fn sort() -> Sort<'st> {
        Self::AST_SORT.into()
    }
    /// Construct a new constante of this sort.
    fn new_const(st: &'st Storage, name: &str) -> Const<'st, Self> {
        let name = st.alloc_str(name);
        let bv = Term::Identifier(qual_ident(name, Some(Self::AST_SORT)));
        let bv = STerm::new(st, bv);
        Const(name, bv.into())
    }
    /// The storage associated with the term.
    fn static_st(&self) -> &'st Storage;
}

/// An trait for typing STM-LIB terms.
///
/// This trait indicates that a type can construct a [`Term`] which is the
/// low-level primitive that is used to define expressions for the SMT solvers
/// to evaluate.
pub trait Sorted<'st>: Into<STerm<'st>> {
    /// The inner type of the term. This is used for [`Const<'st, T>`](Const)
    /// where the inner type is `T`.
    type Inner: Sorted<'st>;
    /// The sort of the term.
    fn sort(&self) -> Sort<'st>;
    /// Check if a sort is of this type.
    fn is_sort(sort: Sort<'st>) -> bool;
    /// The storage associated with any term of this sort.
    fn st(&self) -> &'st Storage;
    /// Constructy the smtlib AST representation of the term with associated
    /// storage.
    fn sterm(self) -> STerm<'st> {
        self.into()
    }
    /// Construct the smtlib AST representation of term.
    fn term(self) -> &'st Term<'st> {
        self.sterm().term()
    }
    /// Casts a dynamically typed term into a concrete type
    fn from_dynamic(d: Dynamic<'st>) -> Self
    where
        Self: From<(STerm<'st>, Sort<'st>)>,
    {
        (d.0, d.1).into()
    }
    /// Casts a dynamically typed term into a concrete type iff the dynamic sort
    /// matches
    fn try_from_dynamic(d: Dynamic<'st>) -> Option<Self>
    where
        Self: From<(STerm<'st>, Sort<'st>)>,
    {
        if Self::is_sort(d.sort()) {
            Some((d.0, d.1).into())
        } else {
            None
        }
    }
    /// Casts the term into a dynamic term which looses static types and stores
    /// the sort dynamically.
    fn into_dynamic(self) -> Dynamic<'st> {
        let sort = self.sort();
        Dynamic::from_term_sort(self.into(), sort)
    }
    /// Construct the term representing `(= self other)`
    fn _eq(self, other: impl IntoWithStorage<'st, Self::Inner>) -> Bool<'st> {
        let other = other.into_with_storage(self.st()).term();
        app(self.st(), "=", (self.term(), other)).into()
    }
    /// Construct the term representing `(distinct self other)`
    fn _neq(self, other: impl IntoWithStorage<'st, Self::Inner>) -> Bool<'st> {
        let other = other.into_with_storage(self.st()).term();
        app(self.st(), "distinct", (self.term(), other)).into()
    }
    /// Wraps the term in a a label, which can be used to extract information
    /// from models at a later point.
    fn labeled(self) -> (Label<Self>, Self::Inner)
    where
        Self::Inner: From<STerm<'st>>,
    {
        let label = Label::generate();
        let name = label.name();
        let name = self.st().alloc_str(&name);
        let args = self.st().alloc_slice(&[Attribute::WithValue(
            Keyword("named"),
            AttributeValue::Symbol(Symbol(name)),
        )]);

        (
            label,
            STerm::new(self.st(), Term::Annotation(self.into().into(), args)).into(),
        )
    }
}
impl<'st, T: Into<STerm<'st>>> From<Const<'st, T>> for STerm<'st> {
    fn from(c: Const<'st, T>) -> Self {
        c.1.into()
    }
}
impl<'st, T: Sorted<'st>> Sorted<'st> for Const<'st, T> {
    type Inner = T;
    fn sort(&self) -> Sort<'st> {
        T::sort(self)
    }
    fn is_sort(sort: Sort<'st>) -> bool {
        T::is_sort(sort)
    }
    fn st(&self) -> &'st Storage {
        self.1.st()
    }
}

impl<'st, T: StaticSorted<'st>> Sorted<'st> for T {
    type Inner = T::Inner;

    fn sort(&self) -> Sort<'st> {
        Self::AST_SORT.into()
    }

    fn is_sort(sort: Sort<'st>) -> bool {
        sort == Self::sort()
    }

    fn st(&self) -> &'st Storage {
        self.static_st()
    }
}

/// Labels are annotations that can be put on expressions to track their
/// satisfiability.
///
/// > **NOTE:** API's for labels are yet to be part of the crate at the time of
/// > writing.
pub struct Label<T>(u64, PhantomData<T>);
impl<T> Label<T> {
    pub(crate) fn generate() -> Self {
        use core::sync::atomic::{AtomicU64, Ordering};
        static NAMED_LABEL_COUNT: AtomicU64 = AtomicU64::new(0);

        let n = NAMED_LABEL_COUNT.fetch_add(1, Ordering::Relaxed);

        Label(n, PhantomData)
    }
    pub(crate) fn name(&self) -> String {
        format!("named-label-{}", self.0)
    }
}

impl<'st, T> From<Const<'st, T>> for Dynamic<'st>
where
    T: Into<Dynamic<'st>>,
{
    fn from(c: Const<'st, T>) -> Self {
        c.1.into()
    }
}
impl<'st> From<Dynamic<'st>> for STerm<'st> {
    fn from(d: Dynamic<'st>) -> Self {
        d.0
    }
}
impl<'st> From<(STerm<'st>, Sort<'st>)> for Dynamic<'st> {
    fn from((t, sort): (STerm<'st>, Sort<'st>)) -> Self {
        Dynamic::from_term_sort(t, sort)
    }
}
impl<'st> Dynamic<'st> {
    /// Construct a dynamic term from a term and a sort.
    pub fn from_term_sort(t: STerm<'st>, sort: Sort<'st>) -> Self {
        Dynamic(t, sort)
    }

    /// Returns the sort of the dynamic term.
    pub fn sort(&self) -> Sort<'st> {
        self.1
    }

    /// Attempt to cast the dynamic into an [`Int`](crate::Int) if the sort
    /// matches.
    pub fn as_int(&self) -> Result<crate::Int<'st>, crate::Error> {
        crate::Int::try_from_dynamic(*self).ok_or_else(|| crate::Error::DynamicCastSortMismatch {
            expected: crate::Int::AST_SORT.to_string(),
            actual: self.1.to_string(),
        })
    }

    /// Attempt to cast the dynamic into a [`Bool`] if the sort
    /// matches.
    pub fn as_bool(&self) -> Result<crate::Bool<'st>, crate::Error> {
        crate::Bool::try_from_dynamic(*self).ok_or_else(|| crate::Error::DynamicCastSortMismatch {
            expected: crate::Bool::AST_SORT.to_string(),
            actual: self.1.to_string(),
        })
    }
}
impl<'st> Sorted<'st> for Dynamic<'st> {
    type Inner = Self;
    fn sort(&self) -> Sort<'st> {
        self.1
    }
    fn is_sort(_sort: Sort<'st>) -> bool {
        true
    }
    fn st(&self) -> &'st Storage {
        self.0.st()
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! impl_op {
    ($ty:ty, $other:ty, $trait:tt, $fn:ident, $op:literal, $a_trait:tt, $a_fn:tt, $a_op:tt) => {
        impl<'st, R> std::ops::$trait<R> for Const<'st, $ty>
        where
            R: IntoWithStorage<'st, $ty>,
        {
            type Output = $ty;
            fn $fn(self, rhs: R) -> Self::Output {
                self.1.binop($op, $crate::terms::IntoWithStorage::into_with_storage(rhs, self.st()))
            }
        }
        impl<'st, R> std::ops::$trait<R> for $ty
        where
            R: IntoWithStorage<'st, $ty>,
        {
            type Output = Self;
            fn $fn(self, rhs: R) -> Self::Output {
                self.binop($op, $crate::terms::IntoWithStorage::into_with_storage(rhs, self.st()))
            }
        }
        impl<'st> std::ops::$trait<Const<'st, $ty>> for $other {
            type Output = $ty;
            fn $fn(self, rhs: Const<'st, $ty>) -> Self::Output {
                // $ty::from(self).binop($op, rhs.1)
                <$other as $crate::terms::IntoWithStorage<'st, $ty>>::into_with_storage(self, rhs.st()).binop($op, rhs.1)
            }
        }
        impl<'st> std::ops::$trait<$ty> for $other {
            type Output = $ty;
            fn $fn(self, rhs: $ty) -> Self::Output {
                // <$ty>::from(self).binop($op, rhs)
                <$other as $crate::terms::IntoWithStorage<'st, $ty>>::into_with_storage(self, rhs.st()).binop($op, rhs)
            }
        }
        impl<'st, R> std::ops::$a_trait<R> for $ty
        where
            R: IntoWithStorage<'st, $ty>,
        {
            fn $a_fn(&mut self, rhs: R) {
                *self = *self $a_op rhs;
            }
        }
    };
}

/// This trait is implemented for types and sequences which can be used as
/// quantified variables in [`forall`] and [`exists`].
pub trait QuantifierVars<'st> {
    /// The concrete sequence of variable declaration which should be quantified
    /// over.
    fn into_vars(self, st: &'st Storage) -> &'st [SortedVar<'st>];
}

impl<'st, A> QuantifierVars<'st> for Const<'st, A>
where
    A: StaticSorted<'st>,
{
    fn into_vars(self, _st: &'st Storage) -> &'st [SortedVar<'st>] {
        let st = self.st();
        st.alloc_slice(&[SortedVar(Symbol(self.0), A::AST_SORT)])
    }
}
macro_rules! impl_quantifiers {
    ($($x:ident $n:tt),+ $(,)?) => {
        impl<'st, $($x,)+> QuantifierVars<'st> for ($(Const<'st, $x>),+)
        where
            $($x: StaticSorted<'st>),+
        {
            fn into_vars(self, st: &'st Storage) -> &'st [SortedVar<'st>] {
                st.alloc_slice(&[
                    $(SortedVar(Symbol((self.$n).0.into()), $x::AST_SORT)),+
                ])
            }
        }
    };
}
impl_quantifiers!(A 0, B 1);
impl_quantifiers!(A 0, B 1, C 2);
impl_quantifiers!(A 0, B 1, C 2, D 3);
impl_quantifiers!(A 0, B 1, C 2, D 3, E 4);

impl<'st> QuantifierVars<'st> for Vec<Const<'st, Dynamic<'st>>> {
    fn into_vars(self, st: &'st Storage) -> &'st [SortedVar<'st>] {
        st.alloc_slice(self.as_slice()).into_vars(st)
    }
}
impl<'st> QuantifierVars<'st> for &'st [Const<'st, Dynamic<'st>>] {
    fn into_vars(self, st: &'st Storage) -> &'st [SortedVar<'st>] {
        if self.is_empty() {
            &[]
        } else {
            st.alloc_slice(
                &self
                    .iter()
                    .map(|v| SortedVar(Symbol(v.0), v.1 .1.ast()))
                    .collect_vec(),
            )
        }
    }
}
impl<'st> QuantifierVars<'st> for &'st [SortedVar<'st>] {
    fn into_vars(self, _st: &'st Storage) -> &'st [SortedVar<'st>] {
        self
    }
}

/// Universally quantifies over `vars` in expression `term`.
pub fn forall<'st>(st: &'st Storage, vars: impl QuantifierVars<'st>, term: Bool<'st>) -> Bool<'st> {
    STerm::new(
        st,
        Term::Forall(vars.into_vars(st), STerm::from(term).into()),
    )
    .into()
}
/// Existentially quantifies over `vars` in expression `term`.
pub fn exists<'st>(st: &'st Storage, vars: impl QuantifierVars<'st>, term: Bool<'st>) -> Bool<'st> {
    STerm::new(
        st,
        Term::Exists(vars.into_vars(st), STerm::from(term).into()),
    )
    .into()
}
