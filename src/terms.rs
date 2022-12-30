use std::marker::PhantomData;

use smtlib_lowlevel::{
    ast::{self, Attribute, AttributeValue, Identifier, QualIdentifier, SortedVar, Term},
    lexicon::{Keyword, Symbol},
};

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

pub trait Quantifiable<Args, Ret> {
    fn apply(self) -> (Vec<SortedVar>, Ret);
}

#[derive(Debug, Clone, Copy)]
pub struct Const<T>(&'static str, T);

impl<T> Const<T> {
    pub fn name(&self) -> &'static str {
        self.0
    }
}
impl<T> std::ops::Deref for Const<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.1
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Bool {
    Const(&'static str),
    Term(&'static Term),
}
impl From<Const<Bool>> for Bool {
    fn from(c: Const<Bool>) -> Self {
        c.1
    }
}
impl std::fmt::Display for Bool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Term::from(*self).fmt(f)
    }
}
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
#[derive(Debug, Clone, Copy)]
pub struct Real(&'static Term);
impl std::fmt::Display for Real {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Term::from(*self).fmt(f)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Dynamic(&'static Term);
impl std::fmt::Display for Dynamic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Term::from(*self).fmt(f)
    }
}

impl From<Int> for Dynamic {
    fn from(i: Int) -> Self {
        Term::from(i).into()
    }
}
impl From<Bool> for Dynamic {
    fn from(b: Bool) -> Self {
        Term::from(b).into()
    }
}

pub trait Sort: Into<Term> {
    type Inner: Sort;
    fn sort() -> ast::Sort;
    fn from_name(name: impl Into<String>) -> Const<Self>
    where
        Self: From<Term>,
    {
        let name = format!("|{}|", name.into());
        Const(
            Box::leak(name.clone().into_boxed_str()),
            Term::Identifier(qual_ident(name, Some(Self::sort()))).into(),
        )
    }
    fn from_dynamic(d: Dynamic) -> Self
    where
        Self: From<Term>,
    {
        d.0.clone().into()
    }
    fn _eq(self, other: impl Into<Self::Inner>) -> Bool {
        fun("=", vec![self.into(), other.into().into()]).into()
    }
    fn _neq(self, other: impl Into<Self::Inner>) -> Bool {
        fun("distinct", vec![self.into(), other.into().into()]).into()
    }
    fn labeled(self) -> (Label<Self>, Self::Inner)
    where
        Self::Inner: From<Term>,
    {
        let label = Label::generate();
        let name = label.name();

        (
            label,
            Term::Annotation(
                Box::new(self.into()),
                vec![Attribute::WithValue(
                    Keyword("named".to_string()),
                    AttributeValue::Symbol(Symbol(name)),
                )],
            )
            .into(),
        )
    }
}
impl<T: Into<Term>> From<Const<T>> for Term {
    fn from(c: Const<T>) -> Self {
        c.1.into()
    }
}
impl<T: Sort> Sort for Const<T> {
    type Inner = T;
    fn sort() -> ast::Sort {
        T::sort()
    }
}
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
impl Sort for Int {
    type Inner = Self;
    fn sort() -> ast::Sort {
        ast::Sort::Sort(Identifier::Simple(Symbol("Int".into())))
    }
}
impl From<i64> for Int {
    fn from(i: i64) -> Self {
        Term::Identifier(qual_ident(i.to_string(), None)).into()
    }
}
impl Int {
    fn binop<T: From<Term>>(self, op: &str, other: Int) -> T {
        fun(op, vec![self.into(), other.into()]).into()
    }
    pub fn gt(self, other: impl Into<Self>) -> Bool {
        self.binop(">", other.into())
    }
    pub fn ge(self, other: impl Into<Self>) -> Bool {
        self.binop(">=", other.into())
    }
    pub fn lt(self, other: impl Into<Self>) -> Bool {
        self.binop("<", other.into())
    }
    pub fn le(self, other: impl Into<Self>) -> Bool {
        self.binop("<=", other.into())
    }
}
impl From<Real> for Term {
    fn from(b: Real) -> Self {
        Term::Identifier(qual_ident(b.to_string(), None))
    }
}
impl Sort for Real {
    type Inner = Self;
    fn sort() -> ast::Sort {
        ast::Sort::Sort(Identifier::Simple(Symbol("Real".into())))
    }
}
impl From<bool> for Bool {
    fn from(b: bool) -> Self {
        let s = match b {
            true => "true",
            false => "false",
        };

        Term::Identifier(qual_ident(s.into(), None)).into()
    }
}
impl From<Bool> for Term {
    fn from(b: Bool) -> Self {
        match b {
            Bool::Const(name) => Term::Identifier(qual_ident(name.into(), None)),
            Bool::Term(t) => t.clone(),
        }
    }
}
impl From<Term> for Bool {
    fn from(t: Term) -> Self {
        Bool::Term(Box::leak(Box::new(t)))
    }
}
impl Sort for Bool {
    type Inner = Self;
    fn sort() -> ast::Sort {
        ast::Sort::Sort(Identifier::Simple(Symbol("Bool".into())))
    }
}
impl Bool {
    fn binop(self, op: &str, other: Bool) -> Self {
        fun(op, vec![self.into(), other.into()]).into()
    }
    pub fn implies(self, other: Bool) -> Bool {
        self.binop("=>", other)
    }
    pub fn ite(self, then: Bool, otherwise: Bool) -> Bool {
        fun("ite", vec![self.into(), then.into(), otherwise.into()]).into()
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
impl From<Term> for Dynamic {
    fn from(t: Term) -> Self {
        Dynamic(Box::leak(Box::new(t)))
    }
}
impl Sort for Dynamic {
    type Inner = Self;
    fn sort() -> ast::Sort {
        ast::Sort::Sort(Identifier::Simple(Symbol("dynamic".into())))
    }
}

impl std::ops::Neg for Int {
    type Output = Self;
    fn neg(self) -> Self::Output {
        fun("-", vec![self.into()]).into()
    }
}
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
impl_op!(Int, i64, Add, add, "+", AddAssign, add_assign, +);
impl_op!(Int, i64, Sub, sub, "-", SubAssign, sub_assign, -);
impl_op!(Int, i64, Mul, mul, "*", MulAssign, mul_assign, *);
impl_op!(Int, i64, Div, div, "div", DivAssign, div_assign, /);
impl_op!(Bool, bool, BitAnd, bitand, "and", BitAndAssign, bitand_assign, &);
impl_op!(Bool, bool, BitOr,  bitor,  "or", BitOrAssign,  bitor_assign,  |);
impl_op!(Bool, bool, BitXor, bitxor, "xor",  BitXorAssign, bitxor_assign, ^);

impl std::ops::Not for Bool {
    type Output = Bool;

    fn not(self) -> Self::Output {
        fun("not", vec![self.into()]).into()
    }
}

pub trait QuantifierVars {
    fn into_vars(self) -> Vec<SortedVar>;
}

impl<A> QuantifierVars for Const<A>
where
    A: Sort,
{
    fn into_vars(self) -> Vec<SortedVar> {
        vec![SortedVar(Symbol(self.0.to_string()), A::sort())]
    }
}
macro_rules! impl_quantifiers {
    ($($x:ident $n:tt),+ $(,)?) => {
        impl<$($x,)+> QuantifierVars for ($(Const<$x>),+)
        where
            $($x: Sort),+
        {
            fn into_vars(self) -> Vec<SortedVar> {
                vec![
                    $(SortedVar(Symbol((self.$n).0.into()), $x::sort())),+
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
impl QuantifierVars for Vec<SortedVar> {
    fn into_vars(self) -> Vec<SortedVar> {
        self
    }
}

pub fn forall(vars: impl QuantifierVars, term: Bool) -> Bool {
    Term::Forall(vars.into_vars(), Box::new(term.into())).into()
}
pub fn exists(vars: impl QuantifierVars, term: Bool) -> Bool {
    Term::Exists(vars.into_vars(), Box::new(term.into())).into()
}
