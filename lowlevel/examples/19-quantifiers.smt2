; So far we have used quantifier-free fragments of first-order logic and some theories
; Reasoning about quantifiers is highly challenging.
; It is often undecidable and highly complex for various decidable (yet restricted) fragments.
; We will talk more about reasoning about quantifiers when working with undecidable fragments later.
; Here, we look at a few examples.

(push 1)
  (assert ; notice that we combine integer and real here -> Z3 supports theory combination
    (exists ((x Int))
        (forall ((y Real))
            (=> (> y x) (> (* y y) 1))
        )
    )
  )
  (echo "there exists an integer x such that the square of every larger real y is greater than 1")
  (check-sat)
  ; sat
(pop 1)

(echo "---------------------------------------------------------")

(push 1)
  (assert
    (forall ((x Real))
        (exists ((y Real))
            (= x (* y y))
        )
    )
  )
  (echo "for every real x there exists a real y such that x = y * y")
  (check-sat)
  ; unknown
(pop 1)


(set-logic QF_UF)
(declare-const |Hello World!| Bool)
(assert (not |Hello World!|))
(check-sat)
(get-model)
