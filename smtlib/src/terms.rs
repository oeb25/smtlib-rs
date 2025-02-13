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

#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct STerm<'st> {
    #[cfg_attr(feature = "serde", serde(skip))]
    st: &'st Storage,
    term: &'st Term<'st>,
}
impl<'st> STerm<'st> {
    pub fn new(st: &'st Storage, term: Term<'st>) -> Self {
        Self {
            st,
            term: st.alloc_term(term),
        }
    }
    pub fn new_from_ref(st: &'st Storage, term: &'st Term<'st>) -> Self {
        Self { st, term }
    }
    pub fn st(self) -> &'st Storage {
        self.st
    }
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

pub(crate) fn fun<'st>(
    st: &'st Storage,
    name: &'st str,
    args: &'st [&'st Term<'st>],
) -> STerm<'st> {
    STerm::new(st, Term::Application(qual_ident(name, None), args))
}
pub(crate) fn fun_vec<'st>(
    st: &'st Storage,
    name: &'st str,
    args: Vec<&'st Term<'st>>,
) -> STerm<'st> {
    STerm::new(
        st,
        Term::Application(qual_ident(name, None), st.alloc_slice(&args)),
    )
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
/// To construct a `Const<'st, T>` call [`T::from_name`](Sort::from_name) where
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

pub trait StaticSorted<'st>: Into<STerm<'st>> + From<STerm<'st>> {
    type Inner: StaticSorted<'st>;
    const SORT: Sort<'st>;
    fn static_sort() -> Sort<'st> {
        Self::SORT
    }
    fn new_const(st: &'st Storage, name: &str) -> Const<'st, Self> {
        let name = st.alloc_str(name);
        let bv = Term::Identifier(qual_ident(name, Some(Self::static_sort().ast())));
        let bv = STerm::new(st, bv);
        Const(name, bv.into())
    }
    fn static_st(&self) -> &'st Storage;
}

/// An trait for statically typing STM-LIB terms.
///
/// This trait indicates that a type can construct a [`Term`] which is the
/// low-level primitive that is used to define expressions for the SMT solvers
/// to evaluate.
pub trait Sorted<'st>: Into<STerm<'st>> {
    /// The inner type of the term. This is used for [`Const<'st, T>`](Const)
    /// where the inner type is `T`.
    type Inner: Sorted<'st>;
    /// The sort of the term
    fn sort(&self) -> Sort<'st>;
    /// The sort of the term
    fn is_sort(sort: &Sort<'st>) -> bool;
    fn st(&self) -> &'st Storage;
    // /// Construct a constant of this sort. See the documentation of [`Const`]
    // /// for more information about constants.
    // fn from_name(name: impl Into<String>) -> Const<Self>
    // where
    //     Self: From<Term>,
    // {
    //     // TODO: Only add |_| if necessary
    //     let name = format!("|{}|", name.into());
    //     Const(
    //         Box::leak(name.clone().into_boxed_str()),
    //         Term::Identifier(qual_ident(name, Some(Self::sort().ast()))).into(),
    //     )
    // }
    fn sterm(self) -> STerm<'st> {
        self.into()
    }
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
    fn into_dynamic(self) -> Dynamic<'st> {
        let sort = self.sort();
        Dynamic::from_term_sort(self.into(), sort)
    }
    /// Construct the term representing `(= self other)`
    fn _eq(self, other: impl IntoWithStorage<'st, Self::Inner>) -> Bool<'st> {
        let other = other.into_with_storage(self.st()).term();
        fun_vec(self.st(), "=", [self.term(), other].to_vec()).into()
    }
    /// Construct the term representing `(distinct self other)`
    fn _neq(self, other: impl IntoWithStorage<'st, Self::Inner>) -> Bool<'st> {
        let other = other.into_with_storage(self.st()).term();
        fun_vec(self.st(), "distinct", [self.term(), other].to_vec()).into()
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
    fn is_sort(sort: &Sort<'st>) -> bool {
        T::is_sort(sort)
    }
    fn st(&self) -> &'st Storage {
        self.1.st()
    }
}

impl<'st, T: StaticSorted<'st>> Sorted<'st> for T {
    type Inner = T::Inner;

    fn sort(&self) -> Sort<'st> {
        Self::static_sort()
    }

    fn is_sort(sort: &Sort<'st>) -> bool {
        sort == &Self::static_sort()
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
    pub fn from_term_sort(t: STerm<'st>, sort: Sort<'st>) -> Self {
        Dynamic(t, sort)
    }

    pub fn sort(&self) -> &Sort<'st> {
        &self.1
    }

    pub fn as_int(&self) -> Result<crate::Int, crate::Error> {
        crate::Int::try_from_dynamic(*self).ok_or_else(|| {
            crate::Error::DynamicCastSortMismatch {
                expected: crate::Int::static_sort().to_string(),
                actual: self.1.to_string(),
                // expected: crate::Int::static_sort(),
                // actual: self.1.clone(),
            }
        })
    }

    pub fn as_bool(&self) -> Result<crate::Bool, crate::Error> {
        crate::Bool::try_from_dynamic(*self).ok_or_else(|| {
            crate::Error::DynamicCastSortMismatch {
                expected: crate::Bool::static_sort().to_string(),
                actual: self.1.to_string(),
                // expected: crate::Bool::static_sort(),
                // actual: self.1.clone(),
            }
        })
    }
}
impl<'st> Sorted<'st> for Dynamic<'st> {
    type Inner = Self;
    fn sort(&self) -> Sort<'st> {
        self.1
    }
    fn is_sort(_sort: &Sort<'st>) -> bool {
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
    fn into_vars(self) -> &'st [SortedVar<'st>];
}

impl<'st, A> QuantifierVars<'st> for Const<'st, A>
where
    A: StaticSorted<'st>,
{
    fn into_vars(self) -> &'st [SortedVar<'st>] {
        let st = self.st();
        st.alloc_slice(&[SortedVar(Symbol(self.0), A::static_sort().ast())])
    }
}
macro_rules! impl_quantifiers {
    ($($x:ident $n:tt),+ $(,)?) => {
        impl<'st, $($x,)+> QuantifierVars<'st> for ($(Const<'st, $x>),+)
        where
            $($x: StaticSorted<'st>),+
        {
            fn into_vars(self) -> &'st [SortedVar<'st>] {
                let st = self.0.st();

                st.alloc_slice(&[
                    $(SortedVar(Symbol((self.$n).0.into()), $x::static_sort().ast())),+
                ])
            }
        }
    };
}
impl_quantifiers!(A 0, B 1);
impl_quantifiers!(A 0, B 1, C 2);
impl_quantifiers!(A 0, B 1, C 2, D 3);
impl_quantifiers!(A 0, B 1, C 2, D 3, E 4);

// impl QuantifierVars for Vec<(Const<Dynamic<'st>>, ast::Sort)> {
//     fn into_vars(self) -> Vec<SortedVar> {
//         self.into_iter()
//             .map(|(v, s)| SortedVar(Symbol(v.0.into()), s))
//             .collect()
//     }
// }
impl<'st> QuantifierVars<'st> for &'st [Const<'st, Dynamic<'st>>] {
    fn into_vars(self) -> &'st [SortedVar<'st>] {
        if self.is_empty() {
            &[]
        } else {
            let st = self.first().unwrap().st();

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
    fn into_vars(self) -> &'st [SortedVar<'st>] {
        self
    }
}

/// Universally quantifies over `vars` in expression `term`.
pub fn forall<'st>(st: &'st Storage, vars: impl QuantifierVars<'st>, term: Bool<'st>) -> Bool<'st> {
    STerm::new(st, Term::Forall(vars.into_vars(), STerm::from(term).into())).into()
}
/// Existentially quantifies over `vars` in expression `term`.
pub fn exists<'st>(st: &'st Storage, vars: impl QuantifierVars<'st>, term: Bool<'st>) -> Bool<'st> {
    STerm::new(st, Term::Exists(vars.into_vars(), STerm::from(term).into())).into()
}
