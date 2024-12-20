#![doc = concat!("```ignore\n", include_str!("./FixedSizeBitVectors.smt2"), "```")]

use itertools::Itertools;
use smtlib_lowlevel::ast::{self, Term};

use crate::{
    Bool,
    sorts::{Index, Sort},
    terms::{Const, Dynamic, Sorted, StaticSorted, fun, qual_ident},
};

/// A bit-vec is a fixed size sequence of boolean values. You can [read more
/// about it
/// here](https://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml), among
/// other places.
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
        i.into_dynamic()
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
            Term::SpecConstant(c) => {
                match c {
                    ast::SpecConstant::Numeral(_) => todo!(),
                    ast::SpecConstant::Decimal(_) => todo!(),
                    ast::SpecConstant::Hexadecimal(h) => h.parse(),
                    ast::SpecConstant::Binary(b) => b.parse(),
                    ast::SpecConstant::String(_) => todo!(),
                }
            }
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

impl<const M: usize> StaticSorted for BitVec<M> {
    type Inner = Self;

    fn static_sort() -> Sort {
        Sort::new_indexed("BitVec", vec![Index::Numeral(M)])
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
    /// Extract a slice of the bit-vec.
    ///
    /// The constraints `I`, `J`, and `M` are:
    ///
    /// ```ignore
    /// M > I >= J
    /// ```
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
    /// Concatenates `self` and `other` bit-vecs to a single contiguous bit-vec
    /// with length `N + M`
    pub fn concat<const N: usize>(self, other: impl Into<BitVec<N>>) -> BitVec<{ N + M }> {
        Term::Application(qual_ident("concat".to_string(), None), vec![
            self.into(),
            other.into().into(),
        ])
        .into()
    }

    // Unary
    /// Calls `(bvnot self)` i.e. bitwise not
    pub fn bvnot(self) -> Self {
        self.unop("bvnot")
    }

    /// Calls `(bvneg self)` i.e. two's complement negation
    pub fn bvneg(self) -> Self {
        self.unop("bvneg")
    }

    // Binary
    /// Calls `(bvnand self other)` i.e. bitwise nand
    pub fn bvnand(self, other: impl Into<Self>) -> Self {
        self.binop("bvnand", other.into())
    }

    /// Calls `(bvnor self other)` i.e. bitwise nor
    pub fn bvnor(self, other: impl Into<Self>) -> Self {
        self.binop("bvnor", other.into())
    }

    /// Calls `(bvxnor self other)` i.e. bitwise xnor
    pub fn bvxnor(self, other: impl Into<Self>) -> Self {
        self.binop("bvxnor", other.into())
    }

    /// Calls `(bvult self other)`
    pub fn bvult(self, other: impl Into<Self>) -> Bool {
        self.binop("bvult", other.into())
    }

    /// Calls `(bvule self other)` i.e. unsigned less or equal
    pub fn bvule(self, other: impl Into<Self>) -> Bool {
        self.binop("bvule", other.into())
    }

    /// Calls `(bvugt self other)` i.e. unsigned greater than
    pub fn bvugt(self, other: impl Into<Self>) -> Bool {
        self.binop("bvugt", other.into())
    }

    /// Calls `(bvuge self other)` i.e. unsigned greater or equal
    pub fn bvuge(self, other: impl Into<Self>) -> Bool {
        self.binop("bvuge", other.into())
    }

    /// Calls `(bvslt self other)` i.e. signed less than
    pub fn bvslt(self, other: impl Into<Self>) -> Bool {
        self.binop("bvslt", other.into())
    }

    /// Calls `(bvsle self other)` i.e. signed less or equal
    pub fn bvsle(self, other: impl Into<Self>) -> Bool {
        self.binop("bvsle", other.into())
    }

    /// Calls `(bvsgt self other)` i.e. signed greater than
    pub fn bvsgt(self, other: impl Into<Self>) -> Bool {
        self.binop("bvsgt", other.into())
    }

    /// Calls `(bvsge self other)` i.e. signed greater or equal
    pub fn bvsge(self, other: impl Into<Self>) -> Bool {
        self.binop("bvsge", other.into())
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
    ($ty:ty, $other:ty, $trait:tt, $fn:ident, $op:ident, $a_trait:tt, $a_fn:tt, $a_op:tt) => {
        impl<const M: usize, R> std::ops::$trait<R> for Const<$ty>
        where
            R: Into<$ty>,
        {
            type Output = $ty;
            fn $fn(self, rhs: R) -> Self::Output {
                self.1.binop(stringify!($op), rhs.into())
            }
        }
        impl<const M: usize, R> std::ops::$trait<R> for $ty
        where
            R: Into<$ty>,
        {
            type Output = Self;
            fn $fn(self, rhs: R) -> Self::Output {
                self.binop(stringify!($op), rhs.into())
            }
        }
        impl<const M: usize> std::ops::$trait<Const<$ty>> for $other {
            type Output = $ty;
            fn $fn(self, rhs: Const<$ty>) -> Self::Output {
                <$ty>::from(self).binop(stringify!($op), rhs.1)
            }
        }
        impl<const M: usize> std::ops::$trait<$ty> for $other {
            type Output = $ty;
            fn $fn(self, rhs: $ty) -> Self::Output {
                <$ty>::from(self).binop(stringify!($op), rhs)
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
        impl<const M: usize> $ty {
            #[doc = concat!("Calls `(", stringify!($op), " self other)`")]
            pub fn $op(self, other: impl Into<Self>) -> Self {
                self.binop(stringify!($op), other.into())
            }
        }
    };
}

impl_op!(BitVec<M>, [bool; M], BitAnd, bitand, bvand, BitAndAssign, bitand_assign, &);
impl_op!(BitVec<M>, [bool; M], BitOr, bitor, bvor, BitOrAssign, bitor_assign, |);
impl_op!(BitVec<M>, [bool; M], BitXor, bitxor, bvxor, BitXorAssign, bitxor_assign, ^);
impl_op!(BitVec<M>, [bool; M], Add, add, bvadd, AddAssign, add_assign, +);
// impl_op!(BitVec<M>, [bool; M], Sub, sub, bvsub, SubAssign, sub_assign, -);
impl_op!(BitVec<M>, [bool; M], Mul, mul, bvmul, MulAssign, mul_assign, *);
impl_op!(BitVec<M>, [bool; M], Div, div, bvudiv, DivAssign, div_assign, /);
impl_op!(BitVec<M>, [bool; M], Rem, rem, bvurem, RemAssign, rem_assign, %);
impl_op!(BitVec<M>, [bool; M], Shr, shr, bvlshr, ShrAssign, shr_assign, >>);
impl_op!(BitVec<M>, [bool; M], Shl, shl, bvshl, ShlAssign, shl_assign, <<);

#[cfg(feature = "const-bit-vec")]
#[cfg(test)]
mod tests {
    use smtlib_lowlevel::backend::Z3Binary;

    use super::BitVec;
    use crate::{Solver, terms::Sorted};

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

        let model = solver.check_sat_with_model()?.expect_sat()?;

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
