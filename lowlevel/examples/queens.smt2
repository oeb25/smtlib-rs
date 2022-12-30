; The N-queens problem is to place N-queens on an N x N chess board such that no two queens threaten each other.
; Let's try to solve that problem for N = 8.
;
; We use N integer-valued variables, x1, x2, ..., xN,
; where xi holds the row of the queen in column i

(declare-const x0 Int)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)
(declare-const x5 Int)
(declare-const x6 Int)
(declare-const x7 Int)

(declare-const N Int)

(assert (= N 8))

; valid positions
(assert
    (and
        (>= x0 0) (< x0 N)
        (>= x1 0) (< x1 N)
        (>= x2 0) (< x2 N)
        (>= x3 0) (< x3 N)
        (>= x4 0) (< x4 N)
        (>= x5 0) (< x5 N)
        (>= x6 0) (< x6 N)
        (>= x7 0) (< x7 N)
    )
)

; one queen for each row
(assert (distinct x0 x1 x2 x3 x4 x5 x6 x7))

; one queen for down diagonals
(assert
    (distinct
        (- x0 0)
        (- x1 1)
        (- x2 2)
        (- x3 3)
        (- x4 4)
        (- x5 5)
        (- x6 6)
        (- x7 7)
    )
)

; one queen for up diagonals
(assert
    (distinct
        (+ x0 0)
        (+ x1 1)
        (+ x2 2)
        (+ x3 3)
        (+ x4 4)
        (+ x5 5)
        (+ x6 6)
        (+ x7 7)
    )
)

(check-sat)
(get-model)
