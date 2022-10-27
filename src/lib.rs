use std::marker::PhantomData;

use ast::{
    Attribute, AttributeValue, Identifier, Keyword, QualIdentifier, SortedVar, Symbol, Term,
};
use itertools::Itertools;

pub mod ast;

fn fun(name: &str, args: Vec<Term>) -> Term {
    Term::QualIdentifier(qual_ident(name.to_string(), None), args)
}
fn qual_ident(s: String, sort: Option<ast::Sort>) -> QualIdentifier {
    QualIdentifier(Identifier::Simple(Symbol(s)), sort)
}

#[derive(Debug, Default)]
pub struct Solver {
    assertions: Vec<Bool>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SatResult {
    Unsat,
    Sat,
    Unknown,
}

impl Solver {
    pub fn new() -> Self {
        // RecFuncDecl

        let _ = ast::Command::DefineFunRec(ast::FunctionDef(
            Symbol("hello".to_string()),
            vec![],
            Int::sort(),
        ));

        Self::default()
    }
    pub fn assert(&mut self, b: Bool) -> &mut Self {
        self.assertions.push(b);
        self
    }
    pub fn to_commands(&self) -> Vec<ast::Command> {
        let consts = self.assertions.iter().flat_map(|b| {
            Term::from(*b)
                .all_consts()
                .into_iter()
                .cloned()
                .collect_vec()
        });

        let mut stmts = vec![];

        for c in consts {
            if let Some(sort) = &c.1 {
                stmts.push(ast::Command::DeclareConst(
                    match c.0 {
                        Identifier::Simple(s) => s,
                        Identifier::Indexed(_, _) => todo!(),
                    },
                    sort.clone(),
                ));
            }
        }

        for a in &self.assertions {
            stmts.push(ast::Command::Assert(Term::from(*a).strip_sort()));
        }

        stmts.push(ast::Command::CheckSat);

        stmts
    }
    pub fn to_smtlib(&self) -> String {
        self.to_commands().iter().format("\n").to_string()
    }
    #[cfg(feature = "z3")]
    pub fn check_z3(&self) -> Result<SatResult, std::io::Error> {
        self.check_using::<std::io::Error>(|src| {
            use std::io::Write;
            use std::process::{Command, Stdio};

            let mut cmd = Command::new("z3")
                .arg("-in")
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .spawn()?;
            let mut stdin = cmd.stdin.take().unwrap();

            write!(stdin, "{src}").unwrap();

            stdin.flush()?;
            drop(stdin);

            Ok(String::from_utf8(cmd.wait_with_output()?.stdout).unwrap())
        })
    }
    pub fn check_using<Err>(
        &self,
        exec: impl FnOnce(String) -> Result<String, Err>,
    ) -> Result<SatResult, Err> {
        match exec(self.to_smtlib())?.trim() {
            "unsat" => Ok(SatResult::Unsat),
            "sat" => Ok(SatResult::Sat),
            "unknown" => Ok(SatResult::Unknown),
            s => todo!("\n{}\n", s.lines().format("\n")),
        }
    }
}

pub trait Quantifiable<Args, Ret> {
    fn apply(self) -> (Vec<SortedVar>, Ret);
}

#[derive(Debug, Clone, Copy)]
pub struct Const<T>(&'static str, T);
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
            Term::QualIdentifier(qual_ident(name, Some(Self::sort())), vec![]).into(),
        )
    }
    fn from_dynamic(d: Dynamic) -> Self
    where
        Self: From<Term>,
    {
        d.0.clone().into()
    }
    fn _eq(self, other: impl Into<Self>) -> Bool {
        fun("=", vec![self.into(), other.into().into()]).into()
    }
    fn _neq(self, other: impl Into<Self>) -> Bool {
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
            Term::Annotate(
                Box::new(self.into()),
                vec![Attribute(
                    Keyword("named".to_string()),
                    Some(AttributeValue::Symbol(Symbol(name))),
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
        ast::Sort(Identifier::Simple(Symbol("Int".into())), vec![])
    }
}
impl From<i64> for Int {
    fn from(i: i64) -> Self {
        Term::QualIdentifier(qual_ident(i.to_string(), None), vec![]).into()
    }
}
impl Int {
    fn binop(self, op: &str, other: Int) -> Self {
        fun(op, vec![self.into(), other.into()]).into()
    }
    pub fn gt(self, other: Int) -> Self {
        self.binop(">", other)
    }
    pub fn ge(self, other: Int) -> Self {
        self.binop(">=", other)
    }
    pub fn lt(self, other: Int) -> Self {
        self.binop("<", other)
    }
    pub fn le(self, other: Int) -> Self {
        self.binop("<=", other)
    }
}
impl From<Real> for Term {
    fn from(b: Real) -> Self {
        todo!()
    }
}
impl From<Term> for Real {
    fn from(t: Term) -> Self {
        todo!()
    }
}
impl Sort for Real {
    type Inner = Self;
    fn sort() -> ast::Sort {
        ast::Sort(Identifier::Simple(Symbol("Real".into())), vec![])
    }
}
impl From<bool> for Bool {
    fn from(b: bool) -> Self {
        let s = match b {
            true => "true",
            false => "false",
        };

        Term::QualIdentifier(qual_ident(s.into(), None), vec![]).into()
    }
}
impl From<Bool> for Term {
    fn from(b: Bool) -> Self {
        match b {
            Bool::Const(name) => Term::QualIdentifier(qual_ident(name.into(), None), vec![]),
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
        ast::Sort(Identifier::Simple(Symbol("Bool".into())), vec![])
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
        ast::Sort(Identifier::Simple(Symbol("dynamic".into())), vec![])
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
impl_op!(Int, i64, Div, div, "/", DivAssign, div_assign, /);
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

pub fn forall(vars: impl QuantifierVars, term: Bool) -> Bool {
    Term::Forall(vars.into_vars(), Box::new(term.into())).into()
}
pub fn exists(vars: impl QuantifierVars, term: Bool) -> Bool {
    Term::Exists(vars.into_vars(), Box::new(term.into())).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int_math() {
        let x = Int::from_name("x");
        let y = Int::from_name("hello");
        let x_named = x.labeled();
        let mut z = 12 + y * 4;
        z += 3;
        let w = x * x + z;
        println!("{w}");
    }

    #[test]
    fn quantifiers() {
        let x = Int::from_name("x");
        let y = Int::from_name("y");

        let res = forall((x, y), (x + 2)._eq(y));
        println!("{}", Term::from(res));
        panic!();
    }
}
