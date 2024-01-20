; transition system
(declare-fun fib_loop (Int Int Int Int) Bool)
(assert
    (forall 
        ((n Int)) 
        (=> 
            (>= n 0)
            (fib_loop 0 1 0 n)
        )
    )
)

(assert
    (forall 
        ((x Int) (y Int) (n Int) (i Int) (x1 Int) (y1 Int))
        (=> 
            (and
                (fib_loop x y i n)
                (< i n)
                (= x1 y)
                (= y1 (+ x y))
            )
            (fib_loop x1 y1 (+ i 1) n)
        )
    )
)

(assert
    (forall 
        ((x Int) (y Int) (n Int) (i Int))
        (=> 
            (and
                (fib_loop x y i n)
                (not (< i n))
                (not (>= n 0))
            )
            false
        )
    )
)

(check-sat)
