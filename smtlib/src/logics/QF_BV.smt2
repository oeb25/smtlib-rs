(logic QF_BV

 :smt-lib-version 2.6
 :smt-lib-release "2017-11-24"
 :written-by "Silvio Ranise, Cesare Tinelli, and Clark Barrett"
 :date "2010-05-02"
 :last-updated "2017-06-13"
 :update-history
 "Note: history only accounts for content changes, not release changes.
  2020-05-20 bvxnor is no longer marked as left associative, as that is
             inconsistent with its meaning as the negation of bvxor.
  2017-06-13 Added that bvxor and bvxnor are left associative
  2017-05-03 Updated to Version 2.6.  Division and remainder operations are no
             longer undefiend when the second operand is 0.  See
             the FixedSizeBitVectors theory definition for details.
  2015-04-25 Updated to Version 2.5.
  2013-06-24 Changed references to Fixed_Size_Bitvectors to FixedSizeBitVectors.
  2011-06-15 Fixed bug in definition of bvsmod.  Previously, it gave an incorrect
             answer when the divisor is negative and goes into the dividend evenly.
 "

:theories (FixedSizeBitVectors)

:language
 "Closed quantifier-free formulas built over an arbitrary expansion of the
  FixedSizeBitVectors signature with free constant symbols over the sorts
  (_ BitVec m) for 0 < m.  Formulas in ite terms must satisfy the same
  restriction as well, with the exception that they need not be closed 
  (because they may be in the scope of a let binder).
 "

:notes
 "For quick reference, the following is a brief and informal summary of the
  legal symbols in this logic and their meaning (formal definitions are found
  either in the FixedSizeBitvectors theory, or in the extensions below).

  Defined in theory FixedSizeBitvectors:

    Bitvector constants:

      - #bX where X is a binary numeral of length m defines the
        bitvector constant with value X and size m.
      - #xX where X is a hexadecimal numeral of length m defines the
        bitvector constant with value X and size 4*m.
 
   Functions:
 
    (concat (_ BitVec i) (_ BitVec j) (_ BitVec m))
      - concatenation of bitvectors of size i and j to get a new bitvector of
        size m, where m = i + j
    ((_ extract i j) (_ BitVec m) (_ BitVec n))
      - extraction of bits i down to j from a bitvector of size m to yield a
        new bitvector of size n, where n = i - j + 1
    (bvnot (_ BitVec m) (_ BitVec m))
      - bitwise negation
    (bvand (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - bitwise and
    (bvor (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - bitwise or
    (bvneg (_ BitVec m) (_ BitVec m))
      - 2's complement unary minus
    (bvadd (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - addition modulo 2^m
    (bvmul (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - multiplication modulo 2^m
    (bvudiv (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - unsigned division, truncating towards 0
    (bvurem (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - unsigned remainder from truncating division
    (bvshl (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - shift left (equivalent to multiplication by 2^x where x is the value of
        the second argument)
    (bvlshr (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - logical shift right (equivalent to unsigned division by 2^x where x is
        the value of the second argument)
    (bvult (_ BitVec m) (_ BitVec m) Bool)
      - binary predicate for unsigned less-than

  Defined below:

    Functions:

    (bvnand (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - bitwise nand (negation of and)
    (bvnor (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - bitwise nor (negation of or)
    (bvxor (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - bitwise exclusive or
    (bvxnor (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - bitwise equivalence (equivalently, negation of bitwise exclusive or)
    (bvcomp (_ BitVec m) (_ BitVec m) (_ BitVec 1))
      - bit comparator: equals #b1 iff all bits are equal
    (bvsub (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - 2's complement subtraction modulo 2^m
    (bvsdiv (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - 2's complement signed division
    (bvsrem (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - 2's complement signed remainder (sign follows dividend)
    (bvsmod (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - 2's complement signed remainder (sign follows divisor)
    (bvashr (_ BitVec m) (_ BitVec m) (_ BitVec m))
      - Arithmetic shift right, like logical shift right except that the most
        significant bits of the result always copy the most significant
        bit of the first argument.

    The following symbols are parameterized by the numeral i, where i >= 1.

    ((_ repeat i) (_ BitVec m) (_ BitVec i*m))
      - ((_ repeat i) x) means concatenate i copies of x

    The following symbols are parameterized by the numeral i, where i >= 0.

    ((_ zero_extend i) (_ BitVec m) (_ BitVec m+i))
      - ((_ zero_extend i) x) means extend x with zeroes to the (unsigned)
        equivalent bitvector of size m+i
    ((_ sign_extend i) (_ BitVec m) (_ BitVec m+i))
      - ((_ sign_extend i) x) means extend x to the (signed) equivalent bitvector
        of size m+i
    ((_ rotate_left i) (_ BitVec m) (_ BitVec m))
      - ((_ rotate_left i) x) means rotate bits of x to the left i times
    ((_ rotate_right i) (_ BitVec m) (_ BitVec m))
      - ((_ rotate_right i) x) means rotate bits of x to the right i times

    (bvule (_ BitVec m) (_ BitVec m) Bool)
      - binary predicate for unsigned less than or equal
    (bvugt (_ BitVec m) (_ BitVec m) Bool)
      - binary predicate for unsigned greater than
    (bvuge (_ BitVec m) (_ BitVec m) Bool)
      - binary predicate for unsigned greater than or equal
    (bvslt (_ BitVec m) (_ BitVec m) Bool)
      - binary predicate for signed less than
    (bvsle (_ BitVec m) (_ BitVec m) Bool)
      - binary predicate for signed less than or equal
    (bvsgt (_ BitVec m) (_ BitVec m) Bool)
      - binary predicate for signed greater than
    (bvsge (_ BitVec m) (_ BitVec m) Bool)
      - binary predicate for signed greater than or equal
 "

:extensions
 "Below, let |exp| denote the integer resulting from the evaluation
  of the arithmetic expression exp.

  - Bitvector Constants:
    (_ bvX n) where X and n are numerals, i.e. (_ bv13 32),
    abbreviates the term #bY of sort (_ BitVec n) such that

    [[#bY]] = nat2bv[n](X) for X=0, ..., 2^n - 1.

    See the specification of the theory's semantics for a definition
    of the functions [[_]] and nat2bv.  Note that this convention implicitly
    considers the numeral X as a number written in base 10.

  - Bitwise operators

    For all terms s,t of sort (_ BitVec m), where 0 < m,

    (bvnand s t) abbreviates (bvnot (bvand s t))
    (bvnor s t) abbreviates (bvnot (bvor s t))
    (bvxor s t) abbreviates (bvor (bvand s (bvnot t)) (bvand (bvnot s) t))
    (bvxnor s t) abbreviates (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))
    (bvcomp s t) abbreviates (bvxnor s t) if m = 1, and
       (bvand (bvxnor ((_ extract |m-1| |m-1|) s) ((_ extract |m-1| |m-1|) t))
              (bvcomp ((_ extract |m-2| 0) s) ((_ extract |m-2| 0) t))) otherwise.

    Additionally, bvxor is left associative, so:

    (bvxor s_1 s_2 ... s_n) abbreviates (bvxor (bvxor s_1 s_2 ...) s_n), and

  - Arithmetic operators

    For all terms s,t of sort (_ BitVec m), where 0 < m,

    (bvsub s t) abbreviates (bvadd s (bvneg t))
    (bvsdiv s t) abbreviates
      (let ((?msb_s ((_ extract |m-1| |m-1|) s))
            (?msb_t ((_ extract |m-1| |m-1|) t)))
        (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
             (bvudiv s t)
        (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
             (bvneg (bvudiv (bvneg s) t))
        (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
             (bvneg (bvudiv s (bvneg t)))
             (bvudiv (bvneg s) (bvneg t))))))
    (bvsrem s t) abbreviates
      (let ((?msb_s ((_ extract |m-1| |m-1|) s))
            (?msb_t ((_ extract |m-1| |m-1|) t)))
        (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
             (bvurem s t)
        (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
             (bvneg (bvurem (bvneg s) t))
        (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
             (bvurem s (bvneg t)))
             (bvneg (bvurem (bvneg s) (bvneg t))))))
    (bvsmod s t) abbreviates
      (let ((?msb_s ((_ extract |m-1| |m-1|) s))
            (?msb_t ((_ extract |m-1| |m-1|) t)))
        (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
              (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
          (let ((u (bvurem abs_s abs_t)))
            (ite (= u (_ bv0 m))
                 u
            (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
                 u
            (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
                 (bvadd (bvneg u) t)
            (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
                 (bvadd u t)
                 (bvneg u))))))))
    (bvule s t) abbreviates (or (bvult s t) (= s t))
    (bvugt s t) abbreviates (bvult t s)
    (bvuge s t) abbreviates (or (bvult t s) (= s t))
    (bvslt s t) abbreviates:
      (or (and (= ((_ extract |m-1| |m-1|) s) #b1)
               (= ((_ extract |m-1| |m-1|) t) #b0))
          (and (= ((_ extract |m-1| |m-1|) s) ((_ extract |m-1| |m-1|) t))
               (bvult s t)))
    (bvsle s t) abbreviates:
      (or (and (= ((_ extract |m-1| |m-1|) s) #b1)
               (= ((_ extract |m-1| |m-1|) t) #b0))
          (and (= ((_ extract |m-1| |m-1|) s) ((_ extract |m-1| |m-1|) t))
               (bvule s t)))
    (bvsgt s t) abbreviates (bvslt t s)
    (bvsge s t) abbreviates (bvsle t s)

  - Other operations

    For all numerals i > 0, j > 1 and 0 < m, and all terms s and t of
    sort (_ BitVec m),

    (bvashr s t) abbreviates 
      (ite (= ((_ extract |m-1| |m-1|) s) #b0)
           (bvlshr s t)
           (bvnot (bvlshr (bvnot s) t)))

    ((_ repeat 1) t) stands for t
    ((_ repeat j) t) abbreviates (concat t ((_ repeat |j-1|) t))

    ((_ zero_extend 0) t) stands for t
    ((_ zero_extend i) t) abbreviates (concat ((_ repeat i) #b0) t)

    ((_ sign_extend 0) t) stands for t
    ((_ sign_extend i) t) abbreviates
      (concat ((_ repeat i) ((_ extract |m-1| |m-1|) t)) t)

    ((_ rotate_left 0) t) stands for t
    ((_ rotate_left i) t) abbreviates t if m = 1, and
      ((_ rotate_left |i-1|)
        (concat ((_ extract |m-2| 0) t) ((_ extract |m-1| |m-1|) t))
      otherwise

    ((_ rotate_right 0) t) stands for t
    ((_ rotate_right i) t) abbreviates t if m = 1, and
      ((_ rotate_right |i-1|)
        (concat ((_ extract 0 0) t) ((_ extract |m-1| 1) t)))
      otherwise
 "
)

