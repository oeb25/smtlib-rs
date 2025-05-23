#![doc = concat!("```ignore\n", include_str!("./FixedSizeBitVectors.smt2"), "```")]
// Note: We include functions defined in QF_BV here.

use itertools::Itertools;
use smtlib_lowlevel::{
    ast::{self, Identifier, Index, QualIdentifier, Term},
    lexicon::{self, Numeral},
    Storage,
};

use crate::{
    sorts::Sort,
    terms::{
        app, qual_ident, ApplicationArgs, Const, Dynamic, IntoWithStorage, STerm, Sorted,
        StaticSorted,
    },
    Bool,
};

/// A bit-vec is a fixed size sequence of boolean values. You can [read more
/// about it
/// here](https://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml), among
/// other places.
#[derive(Debug, Clone, Copy)]
pub struct BitVec<'st, const M: usize>(STerm<'st>);
impl<'st, const M: usize> From<Const<'st, BitVec<'st, M>>> for BitVec<'st, M> {
    fn from(c: Const<'st, BitVec<'st, M>>) -> Self {
        c.1
    }
}
impl<const M: usize> std::fmt::Display for BitVec<'_, M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.term().fmt(f)
    }
}

impl<'st, const M: usize> From<BitVec<'st, M>> for Dynamic<'st> {
    fn from(i: BitVec<'st, M>) -> Self {
        i.into_dynamic()
    }
}

impl<'st, const M: usize> From<BitVec<'st, M>> for STerm<'st> {
    fn from(i: BitVec<'st, M>) -> Self {
        i.0
    }
}
impl<'st, const M: usize> From<STerm<'st>> for BitVec<'st, M> {
    fn from(t: STerm<'st>) -> Self {
        BitVec(t)
    }
}

impl<'st, const M: usize> From<(STerm<'st>, Sort<'st>)> for BitVec<'st, M> {
    fn from((t, _): (STerm<'st>, Sort<'st>)) -> Self {
        t.into()
    }
}

fn i64_to_bit_array<const M: usize>(i: i64) -> [bool; M] {
    std::array::from_fn(|idx| (i >> (M - idx - 1)) & 1 == 1)
}

// #[test]
// fn test_bit_array() {
//     assert_eq!(i64_to_bit_array::<4>(8), [true; 4]);
// }

impl<'st, const M: usize> TryFrom<BitVec<'st, M>> for i64 {
    type Error = std::num::ParseIntError;

    fn try_from(value: BitVec<'st, M>) -> Result<Self, Self::Error> {
        match value.term() {
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
impl<'st, const M: usize> TryFrom<BitVec<'st, M>> for [bool; M] {
    type Error = std::num::ParseIntError;

    fn try_from(value: BitVec<'st, M>) -> Result<Self, Self::Error> {
        Ok(i64_to_bit_array(value.try_into()?))
    }
}

impl<'st, const M: usize> StaticSorted<'st> for BitVec<'st, M> {
    type Inner = Self;
    const AST_SORT: ast::Sort<'static> =
        ast::Sort::new_indexed("BitVec", &[Index::Numeral(lexicon::Numeral::from_usize(M))]);
    fn static_st(&self) -> &'st Storage {
        self.sterm().st()
    }

    fn sort() -> Sort<'st> {
        Self::AST_SORT.into()
    }

    fn new_const(st: &'st Storage, name: &str) -> Const<'st, Self> {
        let name = st.alloc_str(name);
        let bv = Term::Identifier(qual_ident(name, Some(Self::AST_SORT)));
        let bv = STerm::new(st, bv);
        Const(name, bv.into())
    }
}
impl<'st, const M: usize> IntoWithStorage<'st, BitVec<'st, M>> for [bool; M] {
    fn into_with_storage(self, st: &'st Storage) -> BitVec<'st, M> {
        let term = Term::Identifier(qual_ident(
            st.alloc_str(&format!("#b{}", self.iter().map(|x| *x as u8).format(""))),
            None,
        ));
        STerm::new(st, term).into()
    }
}
impl<'st, const M: usize> IntoWithStorage<'st, BitVec<'st, M>> for i64 {
    fn into_with_storage(self, st: &'st Storage) -> BitVec<'st, M> {
        i64_to_bit_array(self).into_with_storage(st)
    }
}
impl<'st, const M: usize> BitVec<'st, M> {
    /// Construct a new bit-vec.
    pub fn new(
        st: &'st Storage,
        value: impl IntoWithStorage<'st, BitVec<'st, M>>,
    ) -> BitVec<'st, M> {
        value.into_with_storage(st)
    }
    fn binop<T: From<STerm<'st>>>(self, op: &'st str, other: BitVec<'st, M>) -> T {
        app(self.st(), op, (self.term(), other.term())).into()
    }
    fn unop<T: From<STerm<'st>>>(self, op: &'st str) -> T {
        app(self.st(), op, self.term()).into()
    }
    fn unop_indexed<T: From<STerm<'st>>>(
        self,
        op: &'st str,
        index: impl IntoIterator<Item = usize>,
    ) -> T {
        let index = index
            .into_iter()
            .map(|i| Index::Numeral(Numeral::from_usize(i)))
            .collect_vec();
        let qual_id =
            QualIdentifier::Identifier(Identifier::indexed(op, self.st().alloc_slice(&index)));

        STerm::new(
            self.st(),
            Term::Application(qual_id, self.term().into_args(self.st())),
        )
        .into()
    }

    #[cfg(feature = "const-bit-vec")]
    /// Extract a slice of the bit-vec.
    ///
    /// The constraints `I`, `J`, and `M` are:
    ///
    /// ```ignore
    /// M > I >= J
    /// ```
    pub fn extract<const I: usize, const J: usize>(self) -> BitVec<'st, { I - J + 1 }> {
        assert!(M > I);
        assert!(I >= J);

        self.extract_(I, J)
    }

    /// Extract a slice of the bit-vec.
    ///
    /// The constraints `i`, `j`, `M`, and `O` are:
    ///
    /// ```ignore
    /// M > i >= j
    /// O = j - i + 1
    /// ```
    ///
    /// Note: This is a version of `BitVec::extract` that does not depend on
    /// unstable feature `generic_const_exprs`. If you're using nightly
    /// consider enabling `"const-bit-vec"` feature flag and
    /// use `BitVec::extract` instead.
    pub fn extract_<const O: usize>(self, i: usize, j: usize) -> BitVec<'st, O> {
        assert!(M > i);
        assert!(i >= j);
        assert_eq!(O, i - j + 1);

        self.unop_indexed("extract", [i, j])
    }

    #[cfg(feature = "const-bit-vec")]
    /// Concatenate `count` copies of `self` to a new bit-vec
    pub fn repeat<const N: usize>(self) -> BitVec<'st, { N * M }> {
        self.repeat_(N)
    }

    /// Concatenate `count` copies of `self` to a new bit-vec
    ///
    /// Note: This is a version of `BitVec::repeat` that does not depend on
    /// unstable feature `generic_const_exprs`. If you're using nightly
    /// consider enabling `"const-bit-vec"` feature flag and
    /// use `BitVec::repeat` instead.
    pub fn repeat_<const O: usize>(self, count: usize) -> BitVec<'st, O> {
        assert!(count > 0);
        assert_eq!(O, M * count);
        self.unop_indexed("repeat", [count])
    }

    #[cfg(feature = "const-bit-vec")]
    /// Concatenates `self` and `other` bit-vecs to a single contiguous bit-vec
    /// with length `N + M`
    pub fn concat<const N: usize>(
        self,
        other: impl Into<BitVec<'st, N>>,
    ) -> BitVec<'st, { N + M }> {
        self.concat_(other)
    }

    /// Concatenates `self` and `other` bit-vecs to a single contiguous bit-vec
    /// with length `N + M`
    ///
    /// Note: This is a version of `BitVec::concat` that does not depend on
    /// unstable feature `generic_const_exprs`. If you're using nightly
    /// consider enabling `"const-bit-vec"` feature flag and
    /// use `BitVec::concat` instead.
    pub fn concat_<const N: usize, const O: usize>(
        self,
        other: impl Into<BitVec<'st, N>>,
    ) -> BitVec<'st, O> {
        assert_eq!(O, N + M);
        app(self.st(), "concat", (self.term(), other.into().term())).into()
    }

    #[cfg(feature = "const-bit-vec")]
    /// Extend the bit-vec with zeros to the left.
    pub fn zero_extend<const I: usize>(self) -> BitVec<'st, { M + I }> {
        self.zero_extend_(I)
    }

    /// Extend the bit-vec with zeros to the left.
    ///
    /// Note: This is a version of `BitVec::zero_extend` that does not depend on
    /// unstable feature `generic_const_exprs`. If you're using nightly
    /// consider enabling `"const-bit-vec"` feature flag and
    /// use `BitVec::zero_extend` instead.
    pub fn zero_extend_<const O: usize>(self, n: usize) -> BitVec<'st, O> {
        assert_eq!(M + n, O);
        self.unop_indexed("zero_extend", [n])
    }

    #[cfg(feature = "const-bit-vec")]
    /// Extend the bit-vec with the sign bit to the left.
    pub fn sign_extend<const I: usize>(self) -> BitVec<'st, { M + I }> {
        self.sign_extend_(I)
    }

    /// Extend the bit-vec with the sign bit to the left.
    ///
    /// Note: This is a version of `BitVec::sign_extend` that does not depend on
    /// unstable feature `generic_const_exprs`. If you're using nightly
    /// consider enabling `"const-bit-vec"` feature flag and
    /// use `BitVec::sign_extend` instead.
    pub fn sign_extend_<const O: usize>(self, n: usize) -> BitVec<'st, O> {
        assert_eq!(M + n, O);
        self.unop_indexed("sign_extend", [n])
    }

    // Indexed

    /// Rotate the bit-vec to the left.
    pub fn rotate_left(self, n: usize) -> Self {
        self.unop_indexed("rotate_left", [n])
    }
    /// Rotate the bit-vec to the right.
    pub fn rotate_right(self, n: usize) -> Self {
        self.unop_indexed("rotate_right", [n])
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
    /// Calls `(bvcomp self other)` i.e. bitwise comparison
    pub fn bvcomp(self, other: impl Into<Self>) -> BitVec<'st, 1> {
        self.binop("bvcomp", other.into())
    }
    /// Calls `(bvsdiv self other)` i.e. signed division
    pub fn bvsdiv(self, other: impl Into<Self>) -> Self {
        self.binop("bvsdiv", other.into())
    }
    /// Calls `(bvsrem self other)` i.e. signed remainder
    /// (sign follows dividend)
    pub fn bvsrem(self, other: impl Into<Self>) -> Self {
        self.binop("bvsrem", other.into())
    }
    /// Calls `(bvsmod self other)` i.e. signed remainder
    /// (sign follows divisor)
    pub fn bvsmod(self, other: impl Into<Self>) -> Self {
        self.binop("bvsmod", other.into())
    }
    /// Calls `(bvashr self other)` i.e. arithmetic shift right
    pub fn bvashr(self, other: impl Into<Self>) -> Self {
        self.binop("bvashr", other.into())
    }
    /// Calls `(bvult self other)`
    pub fn bvult(self, other: impl Into<Self>) -> Bool<'st> {
        self.binop("bvult", other.into())
    }
    /// Calls `(bvule self other)` i.e. unsigned less or equal
    pub fn bvule(self, other: impl Into<Self>) -> Bool<'st> {
        self.binop("bvule", other.into())
    }
    /// Calls `(bvugt self other)` i.e. unsigned greater than
    pub fn bvugt(self, other: impl Into<Self>) -> Bool<'st> {
        self.binop("bvugt", other.into())
    }
    /// Calls `(bvuge self other)` i.e. unsigned greater or equal
    pub fn bvuge(self, other: impl Into<Self>) -> Bool<'st> {
        self.binop("bvuge", other.into())
    }
    /// Calls `(bvslt self other)` i.e. signed less than
    pub fn bvslt(self, other: impl Into<Self>) -> Bool<'st> {
        self.binop("bvslt", other.into())
    }
    /// Calls `(bvsle self other)` i.e. signed less or equal
    pub fn bvsle(self, other: impl Into<Self>) -> Bool<'st> {
        self.binop("bvsle", other.into())
    }
    /// Calls `(bvsgt self other)` i.e. signed greater than
    pub fn bvsgt(self, other: impl Into<Self>) -> Bool<'st> {
        self.binop("bvsgt", other.into())
    }
    /// Calls `(bvsge self other)` i.e. signed greater or equal
    pub fn bvsge(self, other: impl Into<Self>) -> Bool<'st> {
        self.binop("bvsge", other.into())
    }
}

impl<const M: usize> std::ops::Not for BitVec<'_, M> {
    type Output = Self;
    fn not(self) -> Self::Output {
        self.bvnot()
    }
}
impl<const M: usize> std::ops::Neg for BitVec<'_, M> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        self.bvneg()
    }
}

macro_rules! impl_op {
    ($ty:ty, $other:ty, $trait:tt, $fn:ident, $op:ident, $a_trait:tt, $a_fn:tt, $a_op:tt) => {
        impl<'st, const M: usize, R> std::ops::$trait<R> for Const<'st, $ty>
        where
            R: Into<$ty>,
        {
            type Output = $ty;
            fn $fn(self, rhs: R) -> Self::Output {
                self.1.binop(stringify!($op), rhs.into())
            }
        }
        impl<'st, const M: usize, R> std::ops::$trait<R> for $ty
        where
            R: Into<$ty>,
        {
            type Output = Self;
            fn $fn(self, rhs: R) -> Self::Output {
                self.binop(stringify!($op), rhs.into())
            }
        }
        // impl<'st, const M: usize> std::ops::$trait<Const<'st, $ty>> for $other {
        //     type Output = $ty;
        //     fn $fn(self, rhs: Const<'st, $ty>) -> Self::Output {
        //         <$ty>::from(self).binop(stringify!($op), rhs.1)
        //     }
        // }
        // impl<'st, const M: usize> std::ops::$trait<$ty> for $other {
        //     type Output = $ty;
        //     fn $fn(self, rhs: $ty) -> Self::Output {
        //         <$ty>::from(self).binop(stringify!($op), rhs)
        //     }
        // }
        impl<'st, const M: usize, R> std::ops::$a_trait<R> for $ty
        where
            R: Into<$ty>,
        {
            fn $a_fn(&mut self, rhs: R) {
                *self = *self $a_op rhs;
            }
        }
        impl<'st, const M: usize> $ty {
            #[doc = concat!("Calls `(", stringify!($op), " self other)`")]
            pub fn $op(self, other: impl Into<Self>) -> Self {
                self.binop(stringify!($op), other.into())
            }
        }
    };
}

impl_op!(BitVec<'st, M>, [bool; M], BitAnd, bitand, bvand, BitAndAssign, bitand_assign, &);
impl_op!(BitVec<'st, M>, [bool; M], BitOr, bitor, bvor, BitOrAssign, bitor_assign, |);
impl_op!(BitVec<'st, M>, [bool; M], BitXor, bitxor, bvxor, BitXorAssign, bitxor_assign, ^);
impl_op!(BitVec<'st, M>, [bool; M], Add, add, bvadd, AddAssign, add_assign, +);
impl_op!(BitVec<'st, M>, [bool; M], Sub, sub, bvsub, SubAssign, sub_assign, -);
impl_op!(BitVec<'st, M>, [bool; M], Mul, mul, bvmul, MulAssign, mul_assign, *);
impl_op!(BitVec<'st, M>, [bool; M], Div, div, bvudiv, DivAssign, div_assign, /);
impl_op!(BitVec<'st, M>, [bool; M], Rem, rem, bvurem, RemAssign, rem_assign, %);
impl_op!(BitVec<'st, M>, [bool; M], Shr, shr, bvlshr, ShrAssign, shr_assign, >>);
impl_op!(BitVec<'st, M>, [bool; M], Shl, shl, bvshl, ShlAssign, shl_assign, <<);

#[cfg(feature = "const-bit-vec")]
#[cfg(test)]
mod tests {
    use smtlib_lowlevel::{backend::z3_binary::Z3Binary, Storage};

    use super::BitVec;
    use crate::{
        terms::{Sorted, StaticSorted},
        SatResult, Solver,
    };

    #[test]
    fn bit_vec_extract_concat() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let a = BitVec::<6>::new_const(&st, "a");
        let b = BitVec::<4>::new_const(&st, "b");
        let c = BitVec::<10>::new_const(&st, "c");
        let d = BitVec::<6>::new(&st, [true, false, true, true, false, true]);

        let mut solver = Solver::new(&st, Z3Binary::new("z3")?)?;

        solver.assert(a._eq(!d))?;
        solver.assert(c._eq(a.concat(b)))?;
        solver.assert(b._eq(a.extract::<5, 2>()))?;

        let model = solver.check_sat_with_model()?.expect_sat()?;

        let a: [bool; 6] = model.eval(a).unwrap().try_into()?;
        let b: [bool; 4] = model.eval(b).unwrap().try_into()?;
        let c: [bool; 10] = model.eval(c).unwrap().try_into()?;
        insta::assert_ron_snapshot!(a, @"(false, true, false, false, true, false)");
        insta::assert_ron_snapshot!(b, @"(false, true, false, false)");
        insta::assert_ron_snapshot!(c, @"(false, true, false, false, true, false, false, true, false, false)");

        Ok(())
    }

    #[test]
    fn bit_vec_math() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let a = BitVec::<6>::new_const(&st, "a");
        let b = BitVec::<6>::new_const(&st, "b");
        let c = BitVec::<6>::new_const(&st, "c");

        let mut solver = Solver::new(&st, Z3Binary::new("z3")?)?;

        solver.assert(a._eq(10))?;
        solver.assert(b._eq(3))?;
        // solver.assert(c._eq(a % b))?;
        solver.assert(c._eq(a + b))?;

        assert_eq!(solver.check_sat()?, SatResult::Sat);
        let model = solver.get_model()?;

        let a: i64 = model.eval(a).unwrap().try_into()?;
        let b: i64 = model.eval(b).unwrap().try_into()?;
        let c: i64 = model.eval(c).unwrap().try_into()?;
        insta::assert_ron_snapshot!(a, @"10");
        insta::assert_ron_snapshot!(b, @"3");
        insta::assert_ron_snapshot!(c, @"13");

        Ok(())
    }

    #[test]
    fn bit_vec_dynamic() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let a = BitVec::<64>::new_const(&st, "a");

        assert!(BitVec::<64>::try_from_dynamic(a.into_dynamic()).is_some());
        assert!(BitVec::<32>::try_from_dynamic(a.into_dynamic()).is_none());

        Ok(())
    }
}
