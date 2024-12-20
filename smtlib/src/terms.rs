//! Terms are the building blocks for constructing the mathematical expressions
//! used in assertions with [`Solver`](crate::Solver).
//!
//! They are a statically-typed and ergonomic layer on top of
//! [`smtlib_lowlevel::ast::Term`], which provides a more _Rust-like_ API.

use std::marker::PhantomData;

use smtlib_lowlevel::{
    ast::{self, Attribute, AttributeValue, Identifier, QualIdentifier, SortedVar, Term},
    lexicon::{Keyword, Symbol},
};

use crate::{Bool, sorts::Sort};

pub(crate) fn fun(name: &str, args: Vec<Term>) -> Term {
    Term::Application(qual_ident(name.to_string(), None), args)
}
pub(crate) fn qual_ident(s: String, sort: Option<ast::Sort>) -> QualIdentifier {
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
/// To construct a `Const<T>` call [`T::from_name`](Sort::from_name) where `T`
/// implements [`Sort`].
#[derive(Debug, Clone, Copy)]
pub struct Const<T>(pub(crate) &'static str, pub(crate) T);

impl<T> Const<T> {
    /// The name of the constant
    pub fn name(&self) -> &str {
        self.0
    }
}
impl<T> std::ops::Deref for Const<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.1
    }
}

/// This type wraps terms loosing all static type information. It is particular
/// useful when constructing terms dynamically.
#[derive(Debug, Clone, Copy)]
pub struct Dynamic(&'static Term, &'static Sort);
impl std::fmt::Display for Dynamic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Term::from(*self).fmt(f)
    }
}

pub trait StaticSorted: Into<Term> + From<Term> {
    type Inner: StaticSorted;
    fn static_sort() -> Sort;
    fn new_const(name: impl Into<String>) -> Const<Self> {
        let name = name.into();
        let bv = Term::Identifier(qual_ident(name.clone(), Some(Self::static_sort().ast()))).into();
        let name = String::leak(name);
        Const(name, bv)
    }
}

/// An trait for statically typing STM-LIB terms.
///
/// This trait indicates that a type can construct a [`Term`] which is the
/// low-level primitive that is used to define expressions for the SMT solvers
/// to evaluate.
pub trait Sorted: Into<Term> {
    /// The inner type of the term. This is used for [`Const<T>`](Const) where
    /// the inner type is `T`.
    type Inner: Sorted;
    /// The sort of the term
    fn sort(&self) -> Sort;
    /// The sort of the term
    fn is_sort(sort: &Sort) -> bool;
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
    /// Casts a dynamically typed term into a concrete type
    fn from_dynamic(d: Dynamic) -> Self
    where
        Self: From<(Term, Sort)>,
    {
        (d.0.clone(), d.1.clone()).into()
    }
    /// Casts a dynamically typed term into a concrete type iff the dynamic sort
    /// matches
    fn try_from_dynamic(d: Dynamic) -> Option<Self>
    where
        Self: From<(Term, Sort)>,
    {
        if Self::is_sort(d.sort()) {
            Some((d.0.clone(), d.1.clone()).into())
        } else {
            None
        }
    }
    fn into_dynamic(self) -> Dynamic {
        let sort = self.sort();
        Dynamic::from_term_sort(self.into(), sort)
    }
    /// Construct the term representing `(= self other)`
    fn _eq(self, other: impl Into<Self::Inner>) -> Bool {
        fun("=", vec![self.into(), other.into().into()]).into()
    }
    /// Construct the term representing `(distinct self other)`
    fn _neq(self, other: impl Into<Self::Inner>) -> Bool {
        fun("distinct", vec![self.into(), other.into().into()]).into()
    }
    /// Wraps the term in a a label, which can be used to extract information
    /// from models at a later point.
    fn labeled(self) -> (Label<Self>, Self::Inner)
    where
        Self::Inner: From<Term>,
    {
        let label = Label::generate();
        let name = label.name();

        (
            label,
            Term::Annotation(Box::new(self.into()), vec![Attribute::WithValue(
                Keyword("named".to_string()),
                AttributeValue::Symbol(Symbol(name)),
            )])
            .into(),
        )
    }
}
impl<T: Into<Term>> From<Const<T>> for Term {
    fn from(c: Const<T>) -> Self {
        c.1.into()
    }
}
impl<T: Sorted> Sorted for Const<T> {
    type Inner = T;

    fn sort(&self) -> Sort {
        T::sort(self)
    }

    fn is_sort(sort: &Sort) -> bool {
        T::is_sort(sort)
    }
}

impl<T: StaticSorted> Sorted for T {
    type Inner = T::Inner;

    fn sort(&self) -> Sort {
        Self::static_sort()
    }

    fn is_sort(sort: &Sort) -> bool {
        sort == &Self::static_sort()
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

impl<T> From<Const<T>> for Dynamic
where
    T: Into<Dynamic>,
{
    fn from(c: Const<T>) -> Self {
        c.1.into()
    }
}
impl From<Dynamic> for Term {
    fn from(d: Dynamic) -> Self {
        d.0.clone()
    }
}
impl From<(Term, Sort)> for Dynamic {
    fn from((t, sort): (Term, Sort)) -> Self {
        Dynamic::from_term_sort(t, sort)
    }
}
impl Dynamic {
    pub fn from_term_sort(t: Term, sort: Sort) -> Self {
        Dynamic(Box::leak(Box::new(t)), Box::leak(Box::new(sort)))
    }

    pub fn sort(&self) -> &Sort {
        &self.1
    }

    pub fn as_int(&self) -> Result<crate::Int, crate::Error> {
        crate::Int::try_from_dynamic(self.clone()).ok_or_else(|| {
            crate::Error::DynamicCastSortMismatch {
                expected: crate::Int::static_sort(),
                actual: self.1.clone(),
            }
        })
    }

    pub fn as_bool(&self) -> Result<crate::Bool, crate::Error> {
        crate::Bool::try_from_dynamic(self.clone()).ok_or_else(|| {
            crate::Error::DynamicCastSortMismatch {
                expected: crate::Bool::static_sort(),
                actual: self.1.clone(),
            }
        })
    }
}
impl Sorted for Dynamic {
    type Inner = Self;

    fn sort(&self) -> Sort {
        self.1.clone()
    }

    fn is_sort(_sort: &Sort) -> bool {
        true
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! impl_op {
    ($ty:ty, $other:ty, $trait:tt, $fn:ident, $op:literal, $a_trait:tt, $a_fn:tt, $a_op:tt) => {
        impl<R> std::ops::$trait<R> for Const<$ty>
        where
            R: Into<$ty>,
        {
            type Output = $ty;
            fn $fn(self, rhs: R) -> Self::Output {
                self.1.binop($op, rhs.into())
            }
        }
        impl<R> std::ops::$trait<R> for $ty
        where
            R: Into<$ty>,
        {
            type Output = Self;
            fn $fn(self, rhs: R) -> Self::Output {
                self.binop($op, rhs.into())
            }
        }
        impl std::ops::$trait<Const<$ty>> for $other {
            type Output = $ty;
            fn $fn(self, rhs: Const<$ty>) -> Self::Output {
                <$ty>::from(self).binop($op, rhs.1)
            }
        }
        impl std::ops::$trait<$ty> for $other {
            type Output = $ty;
            fn $fn(self, rhs: $ty) -> Self::Output {
                <$ty>::from(self).binop($op, rhs)
            }
        }
        impl<R> std::ops::$a_trait<R> for $ty
        where
            R: Into<$ty>,
        {
            fn $a_fn(&mut self, rhs: R) {
                *self = *self $a_op rhs;
            }
        }
    };
}

/// This trait is implemented for types and sequences which can be used as
/// quantified variables in [`forall`] and [`exists`].
pub trait QuantifierVars {
    /// The concrete sequence of variable declaration which should be quantified
    /// over.
    fn into_vars(self) -> Vec<SortedVar>;
}

impl<A> QuantifierVars for Const<A>
where
    A: StaticSorted,
{
    fn into_vars(self) -> Vec<SortedVar> {
        vec![SortedVar(
            Symbol(self.0.to_string()),
            A::static_sort().ast(),
        )]
    }
}
macro_rules! impl_quantifiers {
    ($($x:ident $n:tt),+ $(,)?) => {
        impl<$($x,)+> QuantifierVars for ($(Const<$x>),+)
        where
            $($x: StaticSorted),+
        {
            fn into_vars(self) -> Vec<SortedVar> {
                vec![
                    $(SortedVar(Symbol((self.$n).0.into()), $x::static_sort().ast())),+
                ]
            }
        }
    };
}
impl_quantifiers!(A 0, B 1);
impl_quantifiers!(A 0, B 1, C 2);
impl_quantifiers!(A 0, B 1, C 2, D 3);
impl_quantifiers!(A 0, B 1, C 2, D 3, E 4);

// impl QuantifierVars for Vec<(Const<Dynamic>, ast::Sort)> {
//     fn into_vars(self) -> Vec<SortedVar> {
//         self.into_iter()
//             .map(|(v, s)| SortedVar(Symbol(v.0.into()), s))
//             .collect()
//     }
// }
impl QuantifierVars for Vec<Const<Dynamic>> {
    fn into_vars(self) -> Vec<SortedVar> {
        self.into_iter()
            .map(|v| SortedVar(Symbol(v.0.into()), v.1.1.ast()))
            .collect()
    }
}
impl QuantifierVars for Vec<SortedVar> {
    fn into_vars(self) -> Vec<SortedVar> {
        self
    }
}

/// Universally quantifies over `vars` in expression `term`.
pub fn forall(vars: impl QuantifierVars, term: Bool) -> Bool {
    Term::Forall(vars.into_vars(), Box::new(term.into())).into()
}
/// Existentially quantifies over `vars` in expression `term`.
pub fn exists(vars: impl QuantifierVars, term: Bool) -> Bool {
    Term::Exists(vars.into_vars(), Box::new(term.into())).into()
}
