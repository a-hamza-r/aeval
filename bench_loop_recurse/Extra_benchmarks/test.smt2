(declare-fun loop (Int Int) Bool)

(assert
	(forall
		((i Int) (n Int))
		(=> (and (>= n 0) (= i 0)) (loop i n))
	)
)

(assert
	(forall
		((i Int) (n Int) (|i'| Int))
		(=> (and (loop i n) (< i n) (= |i'| (+ i 1))) (loop |i'| n))
	)
)

(assert
	(forall
		((i Int) (n Int))
		(=> (and (loop i n) (not (< i n)) (not (= i n))) false)
	)
)

(check-sat)