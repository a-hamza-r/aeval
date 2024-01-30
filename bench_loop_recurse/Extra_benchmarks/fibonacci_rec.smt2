
; recursive definition define-fun-rec
(define-fun-rec fib_rec ((x Int)) Int
    (ite (< x 2) x (+ (fib_rec (- x 1)) (fib_rec (- x 2))))
)


; recursive definition axiom
(declare-fun fib_rec (Int) Int)

(assert 
    (forall
        ((n Int))
        (=>
            (and
                (>= n 0)
                (< n 2)
            )
            (= (fib_rec n) n)
        )
    )
)

(assert
    (forall
        ((n Int))
        (=>
            (>= n 2)
            (= (fib_rec n) (+ (fib_rec (- n 1)) (fib_rec (- n 2))))
        )
    )
) 


(check-sat)
