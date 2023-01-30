(declare-fun inv_0 (Int Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((a Int) (b Int) (M Int) (K Int) (N Int) (c Int) (d Int) (X Int) (Y Int) (|a'| Int) (|b'| Int)) 
(=> 
	(and 
		(= |a'| c) (= |b'| d) (= M X) (= K Y) 
		(= 0 a) (= N (+ (+ (* 2 M) 1) K)) (= b (+ (* 2 M) 1)) (>= M 0) (>= K 0) 
		(= c 1) (= d (+ (* 2 X) 1)) (>= X 0) (>= Y 0) 
		(not (= a N)) (< a (+ (* 2 M) 1)) (= |a'| (+ a 1)) (= |b'| (ite (>= a b) (+ b 1) b))
	) 
	(inv_0 |a'| |b'| M K N c d X Y)
)))

(assert (forall ((a Int) (b Int) (M Int) (K Int) (N Int) (c Int) (d Int) (X Int) (Y Int) (|a'| Int) (|b'| Int) (|c'| Int) (|a''| Int) (|b''| Int)) 
(=> 
	(and 
		(not (= a N)) (< a (+ (* 2 M) 1)) (= |a''| (+ a 1)) (= |b''| (ite (>= a b) (+ b 1) b)) 
		(not (= |a''| N)) (< |a''| (+ (* 2 M) 1)) (= |a'| (+ |a''| 1)) (= |b'| (ite (>= |a''| |b''|) (+ |b''| 1) |b''|))
		(< c (+ (* 2 X) 1)) (= |c'| (+ c 2)) 
		(inv_0 a b M K N c d X Y)
	) 
	(inv_0 |a'| |b'| M K N |c'| d X Y)
)))

(assert (forall ((a Int) (b Int) (M Int) (K Int) (N Int) (c Int) (d Int) (X Int) (Y Int)) 
(=> 
	(and 
		(not (and (not (= a N)) (< a (+ (* 2 M) 1)) (< c (+ (* 2 X) 1))))
		(not (and (= a c) (= b d) (= M X) (= K Y))) 
		(inv_0 a b M K N c d X Y)
	)
	false
)))

(check-sat)