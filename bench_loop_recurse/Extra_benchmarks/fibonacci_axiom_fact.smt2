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


; loop definition from tutorial
(define-fun fib_loop ((x Int) (y Int) (i Int) (n Int)) Bool
    (and (<= 0 i) (<= i n) (= x (fib_rec i)) (= y (fib_rec (+ i 1)))))

; loop definition generated from FreqHorn
;(define-fun fib_loop ((_FH_0 Int)(_FH_1 Int)(_FH_2 Int)(_FH_3 Int)) Bool
;  (and (>= _FH_0 0) (>= _FH_1 1) (>= _FH_2 0) (or (>= _FH_3 0) (> (+ _FH_3 (* (- 1) _FH_2)) 0))))

; transition system fact
(declare-var n Int)

(assert
    (not (=> 
        (>= n 0)
        (fib_loop 0 1 0 n)
    ))
)

(check-sat)
