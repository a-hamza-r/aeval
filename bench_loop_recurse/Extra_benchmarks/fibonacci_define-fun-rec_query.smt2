; recursive definition define-fun-rec
(define-fun-rec fib_rec ((x Int)) Int
    (ite (< x 2) x (+ (fib_rec (- x 1)) (fib_rec (- x 2))))
)


; loop definition from tutorial
(define-fun fib_loop ((x Int) (y Int) (i Int) (n Int)) Bool
    (and (<= 0 i) (<= i n) (= x (fib_rec i)) (= y (fib_rec (+ i 1)))))

; loop definition generated from FreqHorn
;(define-fun fib_loop ((_FH_0 Int)(_FH_1 Int)(_FH_2 Int)(_FH_3 Int)) Bool
;  (and (>= _FH_0 0) (>= _FH_1 1) (>= _FH_2 0) (or (>= _FH_3 0) (> (+ _FH_3 (* (- 1) _FH_2)) 0))))

; transition system query
(declare-var i Int)
(declare-var n Int)
(declare-var x Int)
(declare-var y Int)

(assert
    (not (=> 
        (and
            (fib_loop x y i n)
            (not (< i n))
            (not (= x (fib_rec n)))
        )
        false
    ))
)

(check-sat)
