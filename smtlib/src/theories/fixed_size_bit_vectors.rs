#![doc = concat!("```ignore\n", include_str!("./FixedSizeBitVectors.smt2"), "```")]

use itertools::Itertools;
use smtlib_lowlevel::{
    ast::{self, Identifier, Index, Term},
    lexicon::{Numeral, Symbol},
};

use crate::terms::{fun, qual_ident, Const, Dynamic, Sort};

#[derive(Debug, Clone, Copy)]
pub struct BitVec<const M: usize>(&'static Term);
impl<const M: usize> From<Const<BitVec<M>>> for BitVec<M> {
    fn from(c: Const<BitVec<M>>) -> Self {
        c.1
    }
}
impl<const M: usize> std::fmt::Display for BitVec<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Term::from(*self).fmt(f)
    }
}

impl<const M: usize> From<BitVec<M>> for Dynamic {
    fn from(i: BitVec<M>) -> Self {
        Term::from(i).into()
    }
}

impl<const M: usize> From<BitVec<M>> for Term {
    fn from(i: BitVec<M>) -> Self {
        i.0.clone()
    }
}
impl<const M: usize> From<Term> for BitVec<M> {
    fn from(t: Term) -> Self {
        BitVec(Box::leak(Box::new(t)))
    }
}

fn i64_to_bit_array<const M: usize>(i: i64) -> [bool; M] {
    std::array::from_fn(|idx| (i >> (M - idx - 1)) & 1 == 1)
}

// #[test]
// fn test_bit_array() {
//     assert_eq!(i64_to_bit_array::<4>(8), [true; 4]);
// }

impl<const M: usize> TryFrom<BitVec<M>> for i64 {
    type Error = std::num::ParseIntError;

    fn try_from(value: BitVec<M>) -> Result<Self, Self::Error> {
        match value.0 {
            Term::SpecConstant(c) => match c {
                ast::SpecConstant::Numeral(_) => todo!(),
                ast::SpecConstant::Decimal(_) => todo!(),
                ast::SpecConstant::Hexadecimal(h) => h.parse(),
                ast::SpecConstant::Binary(b) => b.parse(),
                ast::SpecConstant::String(_) => todo!(),
            },
            _ => todo!(),
        }
    }
}
impl<const M: usize> TryFrom<BitVec<M>> for [bool; M] {
    type Error = std::num::ParseIntError;

    fn try_from(value: BitVec<M>) -> Result<Self, Self::Error> {
        Ok(i64_to_bit_array(value.try_into()?))
    }
}

impl<const M: usize> Sort for BitVec<M> {
    type Inner = Self;
    fn sort() -> ast::Sort {
        ast::Sort::Sort(Identifier::Indexed(
            Symbol("BitVec".to_string()),
            vec![Index::Numeral(Numeral(M.to_string()))],
        ))
    }
}
impl<const M: usize> From<[bool; M]> for BitVec<M> {
    fn from(i: [bool; M]) -> Self {
        Term::Identifier(qual_ident(
            format!("#b{}", i.iter().map(|x| *x as u8).format("")),
            None,
        ))
        .into()
    }
}
impl<const M: usize> From<i64> for BitVec<M> {
    fn from(i: i64) -> Self {
        i64_to_bit_array(i).into()
    }
}
impl<const M: usize> BitVec<M> {
    fn binop<T: From<Term>>(self, op: &str, other: BitVec<M>) -> T {
        fun(op, vec![self.into(), other.into()]).into()
    }
    fn unop<T: From<Term>>(self, op: &str) -> T {
        fun(op, vec![self.into()]).into()
    }

    #[cfg(feature = "const-bit-vec")]
    pub fn extract<const I: usize, const J: usize>(self) -> BitVec<{ I - J + 1 }> {
        assert!(M > I);
        assert!(I >= J);

        Term::Application(
            ast::QualIdentifier::Identifier(ast::Identifier::Indexed(
                Symbol("extract".to_string()),
                vec![
                    Index::Numeral(Numeral(I.to_string())),
                    Index::Numeral(Numeral(J.to_string())),
                ],
            )),
            vec![self.into()],
        )
        .into()
    }
    #[cfg(feature = "const-bit-vec")]
    pub fn concat<const N: usize>(self, other: impl Into<BitVec<N>>) -> BitVec<{ N + M }> {
        Term::Application(
            qual_ident("concat".to_string(), None),
            vec![self.into(), other.into().into()],
        )
        .into()
    }

    // Unary
    pub fn bvnot(self) -> Self {
        self.unop("bvnot")
    }
    pub fn bvneg(self) -> Self {
        self.unop("bvneg")
    }

    // Binary
    pub fn bvand(self, other: impl Into<Self>) -> Self {
        self.binop("bvand", other.into())
    }
    pub fn bvor(self, other: impl Into<Self>) -> Self {
        self.binop("bvor", other.into())
    }
    pub fn bvadd(self, other: impl Into<Self>) -> Self {
        self.binop("bvadd", other.into())
    }
    pub fn bvmul(self, other: impl Into<Self>) -> Self {
        self.binop("bvmul", other.into())
    }
    pub fn bvudiv(self, other: impl Into<Self>) -> Self {
        self.binop("bvudiv", other.into())
    }
    pub fn bvurem(self, other: impl Into<Self>) -> Self {
        self.binop("bvurem", other.into())
    }
    pub fn bvshl(self, other: impl Into<Self>) -> Self {
        self.binop("bvshl", other.into())
    }
    pub fn bvlshr(self, other: impl Into<Self>) -> Self {
        self.binop("bvlshr", other.into())
    }
}

impl<const M: usize> std::ops::Not for BitVec<M> {
    type Output = Self;
    fn not(self) -> Self::Output {
        self.bvnot()
    }
}
impl<const M: usize> std::ops::Neg for BitVec<M> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        self.bvneg()
    }
}

macro_rules! impl_op {
    ($ty:ty, $other:ty, $trait:tt, $fn:ident, $op:literal, $a_trait:tt, $a_fn:tt, $a_op:tt) => {
        impl<const M: usize, R> std::ops::$trait<R> for Const<$ty>
        where
            R: Into<$ty>,
        {
            type Output = $ty;
            fn $fn(self, rhs: R) -> Self::Output {
                self.1.binop($op, rhs.into())
            }
        }
        impl<const M: usize, R> std::ops::$trait<R> for $ty
        where
            R: Into<$ty>,
        {
            type Output = Self;
            fn $fn(self, rhs: R) -> Self::Output {
                self.binop($op, rhs.into())
            }
        }
        impl<const M: usize> std::ops::$trait<Const<$ty>> for $other {
            type Output = $ty;
            fn $fn(self, rhs: Const<$ty>) -> Self::Output {
                <$ty>::from(self).binop($op, rhs.1)
            }
        }
        impl<const M: usize> std::ops::$trait<$ty> for $other {
            type Output = $ty;
            fn $fn(self, rhs: $ty) -> Self::Output {
                <$ty>::from(self).binop($op, rhs)
            }
        }
        impl<const M: usize, R> std::ops::$a_trait<R> for $ty
        where
            R: Into<$ty>,
        {
            fn $a_fn(&mut self, rhs: R) {
                *self = *self $a_op rhs;
            }
        }
    };
}

impl_op!(BitVec<M>, [bool; M], BitAnd, bitand, "bvand", BitAndAssign, bitand_assign, &);
impl_op!(BitVec<M>, [bool; M], BitOr, bitor, "bvor", BitOrAssign, bitor_assign, |);
impl_op!(BitVec<M>, [bool; M], Add, add, "bvadd", AddAssign, add_assign, +);
// impl_op!(BitVec<M>, [bool; M], Sub, sub, "bvsub", SubAssign, sub_assign, -);
impl_op!(BitVec<M>, [bool; M], Mul, mul, "bvmul", MulAssign, mul_assign, *);
impl_op!(BitVec<M>, [bool; M], Div, div, "bvudiv", DivAssign, div_assign, /);
impl_op!(BitVec<M>, [bool; M], Rem, rem, "bvurem", RemAssign, rem_assign, %);
impl_op!(BitVec<M>, [bool; M], Shr, shr, "bvshr", ShrAssign, shr_assign, >>);
impl_op!(BitVec<M>, [bool; M], Shl, shl, "bvlshr", ShlAssign, shl_assign, <<);

#[cfg(test)]
mod tests {
    use smtlib_lowlevel::backend::Z3Binary;

    use crate::{terms::Sort, Solver};

    use super::BitVec;

    #[test]
    fn bit_vec_extract_concat() -> Result<(), Box<dyn std::error::Error>> {
        let a = BitVec::<6>::from_name("a");
        let b = BitVec::from_name("b");
        let c = BitVec::from_name("c");
        let d = BitVec::from([true, false, true, true, false, true]);

        let mut solver = Solver::new(Z3Binary::new("z3")?)?;

        solver.assert(a._eq(!d))?;
        solver.assert(b._eq(a.extract::<5, 2>()))?;
        solver.assert(c._eq(a.concat(b)))?;

        solver.check_sat()?;
        let model = solver.get_model()?;

        let a: [bool; 6] = model.eval(a).unwrap().try_into()?;
        let b: [bool; 4] = model.eval(b).unwrap().try_into()?;
        let c: [bool; 10] = model.eval(c).unwrap().try_into()?;
        insta::assert_ron_snapshot!(a, @"(false, true, false, false, true, false)");
        insta::assert_ron_snapshot!(b, @"(false, true, false, false)");
        insta::assert_ron_snapshot!(c, @"(false, true, false, false, true, false, false, true, false, false)");

        Ok(())
    }

    // #[test]
    // fn bit_vec_math() -> Result<(), Box<dyn std::error::Error>> {
    //     let a = BitVec::<6>::from_name("a");
    //     let b = BitVec::<6>::from_name("b");
    //     let c = BitVec::<6>::from_name("c");

    //     let mut solver = Solver::new(Z3Binary::new("z3")?)?;

    //     solver.assert(a._eq(BitVec::<6>::from(10)))?;
    //     solver.assert(b._eq(BitVec::<6>::from(3)))?;
    //     // solver.assert(c._eq(a % b))?;
    //     solver.assert(c._eq(a + b))?;

    //     solver.check_sat()?;
    //     let model = solver.get_model()?;

    //     let a: i64 = model.eval(a).unwrap().try_into()?;
    //     let b: i64 = model.eval(b).unwrap().try_into()?;
    //     let c: i64 = model.eval(c).unwrap().try_into()?;
    //     insta::assert_ron_snapshot!(c, @"");
    //     // insta::assert_ron_snapshot!(b, @"");
    //     // insta::assert_ron_snapshot!(c, @"");

    //     Ok(())
    // }
}
