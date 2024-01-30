; recursive definition axiom
(declare-fun fact_rec (Int) Int)
(assert 
    (forall
        ((n Int))
        (=>
            (and
                (>= n 0)
                (< n 2)
            )
            (= (fact_rec n) 1)
        )
    )
)

(assert
    (forall
        ((n Int))
        (=>
            (>= n 2)
            (= (fact_rec n) (* n (fact_rec (- n 1))))
        )
    )
)


; transition system
(declare-fun fact_loop (Int Int Int Int) Bool)
(assert
    (forall 
        ((n Int)) 
        (=> 
            (>= n 0)
            (fact_loop 1 1 0 n)
        )
    )
)

(assert
    (forall 
        ((x Int) (y Int) (n Int) (i Int) (x1 Int) (y1 Int))
        (=> 
            (and
                (fact_loop x y i n)
                (= x (fact_rec i))
                (= y (fact_rec (+ i 1)))
                (< i n)
                (= x1 y)
                (= y1 (* x (+ i 1)))
            )
            (fact_loop x1 y1 (+ i 1) n)
        )
    )
)

(assert
    (forall 
        ((x Int) (y Int) (n Int) (i Int))
        (=> 
            (and
                (fact_loop x y i n)
                (not (< i n))
                (not (= i n))
                (not (= x (fact_rec n)))
            )
            false
        )
    )
)

(check-sat)
