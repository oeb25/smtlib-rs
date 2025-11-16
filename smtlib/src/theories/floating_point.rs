#![doc = concat!("```ignore\n", include_str!("./FloatingPoint.smt2"), "```")]

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
    theories::fixed_size_bit_vectors::BitVec,
    Bool, Real,
};

/// The SMT-LIB sort for rounding modes in floating-point operations.
#[derive(Debug, Clone, Copy)]
pub struct RoundingMode<'st>(STerm<'st>);

impl<'st> From<Const<'st, RoundingMode<'st>>> for RoundingMode<'st> {
    fn from(c: Const<'st, RoundingMode<'st>>) -> Self {
        c.1
    }
}

impl<'st> std::fmt::Display for RoundingMode<'st> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.term().fmt(f)
    }
}

impl<'st> From<RoundingMode<'st>> for Dynamic<'st> {
    fn from(i: RoundingMode<'st>) -> Self {
        i.into_dynamic()
    }
}

impl<'st> From<RoundingMode<'st>> for STerm<'st> {
    fn from(i: RoundingMode<'st>) -> Self {
        i.0
    }
}

impl<'st> From<STerm<'st>> for RoundingMode<'st> {
    fn from(t: STerm<'st>) -> Self {
        RoundingMode(t)
    }
}

impl<'st> From<(STerm<'st>, Sort<'st>)> for RoundingMode<'st> {
    fn from((t, _s): (STerm<'st>, Sort<'st>)) -> Self {
        // TODO: consider checking sort compatibility if _s is not None
        t.into()
    }
}

impl<'st> StaticSorted<'st> for RoundingMode<'st> {
    type Inner = Self;
    const AST_SORT: ast::Sort<'static> = ast::Sort::new_simple("RoundingMode");

    fn static_st(&self) -> &'st Storage {
        self.st()
    }

    fn sort() -> Sort<'st> {
        Self::AST_SORT.into()
    }

    fn new_const(st: &'st Storage, name: &str) -> Const<'st, Self> {
        let name = st.alloc_str(name);
        let rm = Term::Identifier(qual_ident(name, Some(Self::AST_SORT)));
        let rm = STerm::new(st, rm);
        Const(name, rm.into())
    }
}

impl<'st> RoundingMode<'st> {
    fn new_mode_val(st: &'st Storage, name: &'static str) -> Self {
        STerm::new(st, Term::Identifier(qual_ident(st.alloc_str(name), None))).into()
    }

    /// Round nearest ties to even
    pub fn rne(st: &'st Storage) -> Self {
        Self::new_mode_val(st, "RNE")
    }
    /// Round nearest ties to away
    pub fn rna(st: &'st Storage) -> Self {
        Self::new_mode_val(st, "RNA")
    }
    /// Round toward positive
    pub fn rtp(st: &'st Storage) -> Self {
        Self::new_mode_val(st, "RTP")
    }
    /// Round toward negative
    pub fn rtn(st: &'st Storage) -> Self {
        Self::new_mode_val(st, "RTN")
    }
    /// Round toward zero
    pub fn rtz(st: &'st Storage) -> Self {
        Self::new_mode_val(st, "RTZ")
    }
}

/// A floating-point number, parameterized by exponent bits (EB) and significand
/// bits (SB).
#[derive(Debug, Clone, Copy)]
pub struct FloatingPoint<'st, const EB: usize, const SB: usize>(STerm<'st>);

/// Alias for (_ FloatingPoint 5 11) - IEEE binary16
pub type Float16<'st> = FloatingPoint<'st, 5, 11>;
/// Alias for (_ FloatingPoint 8 24) - IEEE binary32
pub type Float32<'st> = FloatingPoint<'st, 8, 24>;
/// Alias for (_ FloatingPoint 11 53) - IEEE binary64
pub type Float64<'st> = FloatingPoint<'st, 11, 53>;
/// Alias for (_ FloatingPoint 15 113) - IEEE binary128
pub type Float128<'st> = FloatingPoint<'st, 15, 113>;

impl<'st, const EB: usize, const SB: usize> From<Const<'st, FloatingPoint<'st, EB, SB>>>
    for FloatingPoint<'st, EB, SB>
{
    fn from(c: Const<'st, FloatingPoint<'st, EB, SB>>) -> Self {
        c.1
    }
}

impl<const EB: usize, const SB: usize> std::fmt::Display for FloatingPoint<'_, EB, SB> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.term().fmt(f)
    }
}

impl<'st, const EB: usize, const SB: usize> From<FloatingPoint<'st, EB, SB>> for Dynamic<'st> {
    fn from(i: FloatingPoint<'st, EB, SB>) -> Self {
        i.into_dynamic()
    }
}

impl<'st, const EB: usize, const SB: usize> From<FloatingPoint<'st, EB, SB>> for STerm<'st> {
    fn from(i: FloatingPoint<'st, EB, SB>) -> Self {
        i.0
    }
}

impl<'st, const EB: usize, const SB: usize> From<STerm<'st>> for FloatingPoint<'st, EB, SB> {
    fn from(t: STerm<'st>) -> Self {
        FloatingPoint(t)
    }
}

impl<'st, const EB: usize, const SB: usize> From<(STerm<'st>, Sort<'st>)>
    for FloatingPoint<'st, EB, SB>
{
    fn from((t, _): (STerm<'st>, Sort<'st>)) -> Self {
        t.into()
    }
}

impl<'st, const EB: usize, const SB: usize> StaticSorted<'st> for FloatingPoint<'st, EB, SB> {
    type Inner = Self;
    const AST_SORT: ast::Sort<'static> = ast::Sort::new_indexed(
        "FloatingPoint",
        &[
            Index::Numeral(lexicon::Numeral::from_usize(EB)),
            Index::Numeral(lexicon::Numeral::from_usize(SB)),
        ],
    );

    fn static_st(&self) -> &'st Storage {
        self.sterm().st()
    }

    fn sort() -> Sort<'st> {
        Self::AST_SORT.into()
    }

    fn new_const(st: &'st Storage, name: &str) -> Const<'st, Self> {
        let name = st.alloc_str(name);
        let fp = Term::Identifier(qual_ident(name, Some(Self::AST_SORT)));
        let fp = STerm::new(st, fp);
        Const(name, fp.into())
    }
}

trait FloatHelper: Sized {
    const EXPONENT_BITS: u32;
    const SIGNIFICAND_BITS: u32;
    const SIGN_SHIFT: u32 = Self::EXPONENT_BITS + Self::SIGNIFICAND_BITS;
    const EXPONENT_SHIFT: u32 = Self::SIGNIFICAND_BITS;
    fn from_bits_u64(bits: u64) -> Self;
    fn to_bits_u64(self) -> u64;
    fn parse_special(symbol: &str) -> Self;

    fn to_bits_parts(self) -> (i64, i64, i64) {
        let bits = self.to_bits_u64();
        let sign = (bits >> (Self::EXPONENT_BITS + Self::SIGNIFICAND_BITS)) as i64;
        let exponent = ((bits << 1) >> (1 + Self::SIGNIFICAND_BITS)) as i64;
        let significand = ((bits << (1 + Self::EXPONENT_BITS)) >> (1 + Self::EXPONENT_BITS)) as i64;
        (sign, exponent, significand)
    }

    fn from_bits_parts(sign: i64, exponent: i64, significand: i64) -> Self {
        let bits = ((sign as u64) << Self::SIGN_SHIFT)
            | ((exponent as u64) << Self::EXPONENT_SHIFT)
            | (significand as u64);
        Self::from_bits_u64(bits)
    }
}

impl FloatHelper for f32 {
    const EXPONENT_BITS: u32 = 8;
    const SIGNIFICAND_BITS: u32 = 23;

    fn from_bits_u64(bits: u64) -> Self {
        f32::from_bits(bits as u32)
    }
    fn to_bits_u64(self) -> u64 {
        self.to_bits() as u64
    }
    fn parse_special(symbol: &str) -> Self {
        match symbol {
            "+zero" => 0.0,
            "-zero" => -0.0,
            "+oo" => f32::INFINITY,
            "-oo" => f32::NEG_INFINITY,
            "NaN" => f32::NAN,
            _ => panic!("Unknown floating-point constant: {}", symbol),
        }
    }
}

impl FloatHelper for f64 {
    const EXPONENT_BITS: u32 = 11;
    const SIGNIFICAND_BITS: u32 = 52;

    fn from_bits_u64(bits: u64) -> Self {
        f64::from_bits(bits)
    }
    fn to_bits_u64(self) -> u64 {
        self.to_bits()
    }
    fn parse_special(symbol: &str) -> Self {
        match symbol {
            "+zero" => 0.0,
            "-zero" => -0.0,
            "+oo" => f64::INFINITY,
            "-oo" => f64::NEG_INFINITY,
            "NaN" => f64::NAN,
            _ => panic!("Unknown floating-point constant: {}", symbol),
        }
    }
}

impl<'st> IntoWithStorage<'st, Float32<'st>> for f32 {
    fn into_with_storage(self, st: &'st Storage) -> Float32<'st> {
        let (sign, exponent, significand) = self.to_bits_parts();
        Float32::fp::<23>(
            st,
            BitVec::new(st, sign),
            BitVec::new(st, exponent),
            BitVec::new(st, significand),
        )
    }
}

impl<'st> IntoWithStorage<'st, Float64<'st>> for f64 {
    fn into_with_storage(self, st: &'st Storage) -> Float64<'st> {
        let (sign, exponent, significand) = self.to_bits_parts();
        Float64::fp::<52>(
            st,
            BitVec::new(st, sign),
            BitVec::new(st, exponent),
            BitVec::new(st, significand),
        )
    }
}

fn spec_constant_to_i64<'st>(value: &ast::SpecConstant<'st>) -> i64 {
    match value {
        ast::SpecConstant::Numeral(n) => n.into_u128().unwrap().try_into().unwrap(),
        ast::SpecConstant::Hexadecimal(h) => h.parse().unwrap(),
        ast::SpecConstant::Binary(b) => b.parse().unwrap(),
        _ => panic!("Unsupported constant type for bit conversion: {:?}", value),
    }
}

fn term_to_i64<'st>(value: &Term<'st>) -> i64 {
    match value {
        Term::SpecConstant(spec_constant) => spec_constant_to_i64(spec_constant),
        _ => panic!("Expected spec constant, got: {:?}", value),
    }
}

fn try_float_from_term<F: FloatHelper>(term: &Term) -> Result<F, std::num::ParseIntError> {
    Ok(match term {
        Term::Identifier(QualIdentifier::Identifier(Identifier::Indexed(symbol, _))) => {
            F::parse_special(symbol.0)
        }
        Term::Application(QualIdentifier::Identifier(Identifier::Simple(symbol)), args) => {
            assert_eq!(symbol.0, "fp");
            let sign = term_to_i64(args[0]);
            let exponent = term_to_i64(args[1]);
            let significand = term_to_i64(args[2]);
            F::from_bits_parts(sign, exponent, significand)
        }
        _ => panic!("Unexpected term: {:?}", term),
    })
}

impl<'st> TryFrom<Float32<'st>> for f32 {
    type Error = std::num::ParseIntError;

    fn try_from(value: Float32<'st>) -> Result<Self, Self::Error> {
        try_float_from_term(value.term())
    }
}

impl<'st> TryFrom<Float64<'st>> for f64 {
    type Error = std::num::ParseIntError;

    fn try_from(value: Float64<'st>) -> Result<Self, Self::Error> {
        try_float_from_term(value.term())
    }
}

impl<'st, const EB: usize, const SB: usize> FloatingPoint<'st, EB, SB> {
    /// Construct a new bit-vec.
    pub fn new(
        st: &'st Storage,
        value: impl IntoWithStorage<'st, FloatingPoint<'st, EB, SB>>,
    ) -> FloatingPoint<'st, EB, SB> {
        value.into_with_storage(st)
    }

    fn st(&self) -> &'st Storage {
        self.0.st()
    }
    fn term(&self) -> STerm<'st> {
        self.0
    }

    fn app_fn_indexed_args<T: From<STerm<'st>>>(
        st: &'st Storage,
        op: &'st str,
        indices: impl IntoIterator<Item = usize>,
        args: impl ApplicationArgs<'st>,
    ) -> T {
        let index_nodes = indices
            .into_iter()
            .map(|i| Index::Numeral(Numeral::from_usize(i)))
            .collect::<Vec<_>>();
        let qual_id = QualIdentifier::Identifier(Identifier::indexed(
            st.alloc_str(op),
            st.alloc_slice(&index_nodes),
        ));
        STerm::new(st, Term::Application(qual_id, args.into_args(st))).into()
    }

    fn unop_rm_indexed<T: From<STerm<'st>>>(
        self,
        op: &'st str,
        rm: RoundingMode<'st>,
        index_val: usize,
    ) -> T {
        Self::app_fn_indexed_args(self.st(), op, [index_val], (rm.term(), self.term()))
    }

    fn op_const_indexed<T: From<STerm<'st>>>(
        st: &'st Storage,
        op: &'st str,
        indices: impl IntoIterator<Item = usize>,
    ) -> T {
        let index_nodes = indices
            .into_iter()
            .map(|i| Index::Numeral(Numeral::from_usize(i)))
            .collect::<Vec<_>>();
        let qual_id = QualIdentifier::Identifier(Identifier::indexed(
            st.alloc_str(op),
            st.alloc_slice(&index_nodes),
        ));
        STerm::new(st, Term::Identifier(qual_id)).into()
    }

    // Value constructors

    /// Creates a floating-point value from sign, exponent, and significand
    /// bit-vectors. `i = sb - 1`
    ///
    /// Note: The SB_1 parameter is a workaround for
    /// `#![feature(generic_const_exprs)]`.
    pub fn fp<const SB_1: usize>(
        st: &'st Storage,
        sign: BitVec<'st, 1>,
        exponent: BitVec<'st, EB>,
        significand: BitVec<'st, SB_1>,
    ) -> Self {
        assert_eq!(SB_1, SB - 1);
        // The SMT LIB theory states i = sb - 1.
        // The BitVec type ensures the size of significand is SB -1.
        app(st, "fp", (sign.term(), exponent.term(), significand.term())).into()
    }

    /// Positive infinity
    pub fn plus_oo(st: &'st Storage) -> Self {
        Self::op_const_indexed(st, "+oo", [EB, SB])
    }

    /// Negative infinity
    pub fn minus_oo(st: &'st Storage) -> Self {
        Self::op_const_indexed(st, "-oo", [EB, SB])
    }

    /// Positive zero
    pub fn plus_zero(st: &'st Storage) -> Self {
        Self::op_const_indexed(st, "+zero", [EB, SB])
    }

    /// Negative zero
    pub fn minus_zero(st: &'st Storage) -> Self {
        Self::op_const_indexed(st, "-zero", [EB, SB])
    }

    /// Not a Number
    pub fn nan(st: &'st Storage) -> Self {
        Self::op_const_indexed(st, "NaN", [EB, SB])
    }

    // Operators
    fn unop<T: From<STerm<'st>>>(self, op: &'st str) -> T {
        app(self.st(), op, self.term()).into()
    }

    fn binop<T: From<STerm<'st>>>(self, op: &'st str, other: Self) -> T {
        app(self.st(), op, (self.term(), other.term())).into()
    }

    fn ternop_rm<T: From<STerm<'st>>>(
        self,
        op: &'st str,
        rm: RoundingMode<'st>,
        other1: Self,
        other2: Self,
    ) -> T {
        app(
            self.st(),
            op,
            [rm.term(), self.term(), other1.term(), other2.term()],
        )
        .into()
    }

    fn binop_rm<T: From<STerm<'st>>>(self, op: &'st str, rm: RoundingMode<'st>, other: Self) -> T {
        app(self.st(), op, (rm.term(), self.term(), other.term())).into()
    }

    fn unop_rm<T: From<STerm<'st>>>(self, op: &'st str, rm: RoundingMode<'st>) -> T {
        app(self.st(), op, (rm.term(), self.term())).into()
    }

    /// Absolute value
    pub fn fp_abs(self) -> Self {
        self.unop("fp.abs")
    }

    /// Negation
    pub fn fp_neg(self) -> Self {
        self.unop("fp.neg")
    }

    /// Addition
    pub fn fp_add(self, rm: RoundingMode<'st>, other: Self) -> Self {
        self.binop_rm("fp.add", rm, other)
    }

    /// Subtraction
    pub fn fp_sub(self, rm: RoundingMode<'st>, other: Self) -> Self {
        self.binop_rm("fp.sub", rm, other)
    }

    /// Multiplication
    pub fn fp_mul(self, rm: RoundingMode<'st>, other: Self) -> Self {
        self.binop_rm("fp.mul", rm, other)
    }

    /// Division
    pub fn fp_div(self, rm: RoundingMode<'st>, other: Self) -> Self {
        self.binop_rm("fp.div", rm, other)
    }

    /// Fused multiplication and addition: `(self * other1) + other2`
    pub fn fp_fma(self, rm: RoundingMode<'st>, other1: Self, other2: Self) -> Self {
        self.ternop_rm("fp.fma", rm, other1, other2)
    }

    /// Square root
    pub fn fp_sqrt(self, rm: RoundingMode<'st>) -> Self {
        self.unop_rm("fp.sqrt", rm)
    }

    /// Remainder: `self - other * n`, where `n` in Z is nearest to `self/other`
    pub fn fp_rem(self, other: Self) -> Self {
        self.binop("fp.rem", other)
    }

    /// Rounding to integral
    pub fn fp_round_to_integral(self, rm: RoundingMode<'st>) -> Self {
        self.unop_rm("fp.roundToIntegral", rm)
    }

    /// Minimum
    pub fn fp_min(self, other: Self) -> Self {
        self.binop("fp.min", other)
    }

    /// Maximum
    pub fn fp_max(self, other: Self) -> Self {
        self.binop("fp.max", other)
    }

    /// Less than or equal
    pub fn fp_leq(self, other: Self) -> Bool<'st> {
        self.binop("fp.leq", other)
    }

    /// Less than
    pub fn fp_lt(self, other: Self) -> Bool<'st> {
        self.binop("fp.lt", other)
    }

    /// Greater than or equal
    pub fn fp_geq(self, other: Self) -> Bool<'st> {
        self.binop("fp.geq", other)
    }

    /// Greater than
    pub fn fp_gt(self, other: Self) -> Bool<'st> {
        self.binop("fp.gt", other)
    }

    /// IEEE 754-2008 equality
    pub fn fp_eq(self, other: Self) -> Bool<'st> {
        self.binop("fp.eq", other)
    }

    // Classification
    /// Is normal
    pub fn fp_is_normal(self) -> Bool<'st> {
        self.unop("fp.isNormal")
    }
    /// Is subnormal
    pub fn fp_is_subnormal(self) -> Bool<'st> {
        self.unop("fp.isSubnormal")
    }
    /// Is zero
    pub fn fp_is_zero(self) -> Bool<'st> {
        self.unop("fp.isZero")
    }
    /// Is infinite
    pub fn fp_is_infinite(self) -> Bool<'st> {
        self.unop("fp.isInfinite")
    }
    /// Is NaN
    pub fn fp_is_nan(self) -> Bool<'st> {
        self.unop("fp.isNaN")
    }
    /// Is negative
    pub fn fp_is_negative(self) -> Bool<'st> {
        self.unop("fp.isNegative")
    }
    /// Is positive
    pub fn fp_is_positive(self) -> Bool<'st> {
        self.unop("fp.isPositive")
    }

    // Conversions

    /// From single bitstring representation in IEEE 754-2008 interchange
    /// format. `M = EB + SB`
    pub fn to_fp_from_bit_vec<const M: usize>(st: &'st Storage, bv: BitVec<'st, M>) -> Self {
        assert_eq!(M, EB + SB, "BitVec size M must be EB + SB");
        Self::app_fn_indexed_args(st, "to_fp", [EB, SB], bv.term())
    }

    /// From another floating point sort
    pub fn to_fp_from_fp<const MB: usize, const NB: usize>(
        st: &'st Storage,
        rm: RoundingMode<'st>,
        fp_other: FloatingPoint<'st, MB, NB>,
    ) -> Self {
        Self::app_fn_indexed_args(st, "to_fp", [EB, SB], (rm.term(), fp_other.term()))
    }

    /// From real
    pub fn to_fp_from_real(st: &'st Storage, rm: RoundingMode<'st>, real: Real<'st>) -> Self {
        Self::app_fn_indexed_args(st, "to_fp", [EB, SB], (rm.term(), real.term()))
    }

    /// From signed machine integer, represented as a 2's complement bit vector
    pub fn to_fp_from_signed_bit_vec<const M: usize>(
        st: &'st Storage,
        rm: RoundingMode<'st>,
        bv: BitVec<'st, M>,
    ) -> Self {
        Self::app_fn_indexed_args(st, "to_fp", [EB, SB], (rm.term(), bv.term()))
    }

    /// From unsigned machine integer, represented as bit vector
    pub fn to_fp_from_unsigned_bit_vec<const M: usize>(
        st: &'st Storage,
        rm: RoundingMode<'st>,
        bv: BitVec<'st, M>,
    ) -> Self {
        Self::app_fn_indexed_args(st, "to_fp_unsigned", [EB, SB], (rm.term(), bv.term()))
    }

    /// To unsigned machine integer, represented as a bit vector
    pub fn fp_to_ubv<const M: usize>(self, rm: RoundingMode<'st>) -> BitVec<'st, M> {
        self.unop_rm_indexed("fp.to_ubv", rm, M)
    }

    /// To signed machine integer, represented as a 2's complement bit vector
    pub fn fp_to_sbv<const M: usize>(self, rm: RoundingMode<'st>) -> BitVec<'st, M> {
        self.unop_rm_indexed("fp.to_sbv", rm, M)
    }

    /// To real
    pub fn fp_to_real(self) -> Real<'st> {
        self.unop("fp.to_real")
    }
}

#[cfg(test)]
mod tests {
    use smtlib_lowlevel::{backend::z3_binary::Z3Binary, StderrLogger, Storage};

    use super::*;
    use crate::{terms::Sorted, theories::fixed_size_bit_vectors::BitVec, SatResult, Solver};

    fn test_solver<'a>(st: &'a Storage) -> Solver<'a, Z3Binary> {
        let mut res = Solver::new(st, Z3Binary::new("z3").unwrap()).unwrap();
        res.set_logger(StderrLogger);
        res
    }

    #[test]
    fn test_fp_convert_rust_floats() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let mut solver = test_solver(&st);

        let f32_bv_sign = BitVec::new_const(&st, "f32_bv_sign");
        let f64_bv_sign = BitVec::new_const(&st, "f64_bv_sign");
        let f32_bv_exponent = BitVec::new_const(&st, "f32_bv_exponent");
        let f64_bv_exponent = BitVec::new_const(&st, "f64_bv_exponent");
        let f32_bv_significand = BitVec::new_const(&st, "f32_bv_significand");
        let f64_bv_significand = BitVec::new_const(&st, "f64_bv_significand");

        let f32_bv = Float32::fp::<23>(
            &st,
            f32_bv_sign.into(),
            f32_bv_exponent.into(),
            f32_bv_significand.into(),
        );

        let f64_bv = Float64::fp::<52>(
            &st,
            f64_bv_sign.into(),
            f64_bv_exponent.into(),
            f64_bv_significand.into(),
        );

        let f32_const = Float32::new_const(&st, "f32_const");
        let f64_const = Float64::new_const(&st, "f64_const");

        for f in [
            0.0,
            -0.0,
            1.0,
            1. / 3.,
            -1. / 3.,
            123456.789,
            f64::MIN,
            f64::MAX,
            f64::MIN_POSITIVE,
            f64::EPSILON,
            f64::INFINITY,
            f64::NEG_INFINITY,
        ] {
            let model = solver.scope(|solver| {
                solver.assert(f64_const._eq(f))?;
                solver.assert(f32_const._eq(f as f32))?;
                solver.assert(f64_bv._eq(f))?;
                solver.assert(f32_bv._eq(f as f32))?;
                solver.check_sat()?;
                solver.get_model()
            })?;
            let f_model: f64 = model.eval(f64_const).unwrap().try_into()?;
            let f_model_32: f32 = model.eval(f32_const).unwrap().try_into()?;
            assert_eq!(f_model, f);
            assert_eq!(f_model_32, f as f32);
        }

        Ok(())
    }

    #[test]
    fn test_fp_constants_and_classification() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let mut solver = test_solver(&st);

        let p_zero = Float32::plus_zero(&st);
        let n_zero = Float32::minus_zero(&st);
        let p_inf = Float32::plus_oo(&st);
        let n_inf = Float32::minus_oo(&st);
        let nan = Float32::nan(&st);

        solver.assert(p_zero.fp_is_zero())?;
        solver.assert(n_zero.fp_is_zero())?;
        solver.assert(p_inf.fp_is_infinite())?;
        solver.assert(p_inf.fp_is_positive())?;
        solver.assert(n_inf.fp_is_infinite())?;
        solver.assert(n_inf.fp_is_negative())?;
        solver.assert(nan.fp_is_nan())?;

        solver.assert(!p_zero.fp_is_nan())?;
        solver.assert(!p_inf.fp_is_nan())?;

        assert_eq!(solver.check_sat()?, SatResult::Sat);
        Ok(())
    }

    #[test]
    fn test_fp_abs_neg() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let mut solver = test_solver(&st);

        let neg_two = Float32::new(&st, -2.0f32);
        let abs_neg_two = neg_two.fp_abs();
        let neg_neg_two = neg_two.fp_neg();

        solver.assert(abs_neg_two._eq(2.0))?;
        solver.assert(neg_neg_two._eq(2.0))?;

        solver.assert(neg_two.fp_is_negative())?;
        solver.assert(!neg_two.fp_is_positive())?;
        solver.assert(!abs_neg_two.fp_is_negative())?;
        solver.assert(abs_neg_two.fp_is_positive())?;

        assert_eq!(solver.check_sat()?, SatResult::Sat);
        Ok(())
    }

    #[test]
    fn test_fp_add() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let mut solver = test_solver(&st);
        let rne = RoundingMode::rne(&st);
        let one = Float32::new(&st, 1.0f32);
        let sum_one_one = one.fp_add(rne, one);
        solver.assert(sum_one_one._eq(2.0))?;

        assert_eq!(solver.check_sat()?, SatResult::Sat);
        Ok(())
    }

    #[test]
    fn test_fp_fma() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let mut solver = test_solver(&st);
        let rne = RoundingMode::rne(&st);

        let one = Float32::new(&st, 1.0f32);
        let two = Float32::new(&st, 2.0f32);
        let three = Float32::new(&st, 3.0f32);

        let result = one.fp_fma(rne, two, three); // (one * two) + three
        solver.assert(result._eq(5.0f32))?;

        assert_eq!(solver.check_sat()?, SatResult::Sat);
        Ok(())
    }

    #[test]
    fn test_to_fp_from_bit_vec() -> Result<(), Box<dyn std::error::Error>> {
        const EXP_BITS_F32: usize = 8;
        const SIG_BITS_F32: usize = 24;

        let st = Storage::new();
        let mut solver = test_solver(&st);

        let ieee_1_0_val: i64 = 0x3f800000;
        let ieee_1_0_bv: BitVec<{ EXP_BITS_F32 + SIG_BITS_F32 }> = BitVec::new(&st, ieee_1_0_val);

        let fp_val = Float32::to_fp_from_bit_vec(&st, ieee_1_0_bv);
        solver.assert(fp_val._eq(1.0))?;

        assert_eq!(solver.check_sat()?, SatResult::Sat);
        Ok(())
    }

    #[test]
    fn test_fp_to_ubv() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let mut solver = test_solver(&st);
        let rtz = RoundingMode::rtz(&st);
        let rne = RoundingMode::rne(&st);

        let two_fp = Float32::new(&st, 2.0f32);
        solver.assert(two_fp.fp_to_ubv::<42>(rtz)._eq(2i64))?;
        solver.assert(two_fp.fp_to_ubv::<42>(rne)._eq(2i64))?;

        let two_point_75_fp = Float32::new(&st, 2.75f32);
        solver.assert(two_point_75_fp.fp_to_ubv::<42>(rtz)._eq(2i64))?;
        solver.assert(two_point_75_fp.fp_to_ubv::<42>(rne)._eq(3i64))?;

        assert_eq!(solver.check_sat()?, SatResult::Sat);
        Ok(())
    }
}
