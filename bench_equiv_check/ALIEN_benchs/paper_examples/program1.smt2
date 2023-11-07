(declare-fun inv_0 (Int Int Int Int Int) Bool)

(assert (forall ((a Int) (b Int) (M Int) (K Int) (N Int)) 
(=> 
	(and 
		(= 0 a) (= N (+ (+ (* 2 M) 1) K)) (= b (+ (* 2 M) 1)) (>= M 0) (>= K 0)
	) 
	(inv_0 a b M K N)
)))

(assert (forall ((a Int) (b Int) (M Int) (K Int) (N Int) (|a'| Int) (|b'| Int)) 
(=> 
	(and 
		(not (= a N)) (= |a'| (+ a 1)) (= |b'| (ite (>= a b) (+ b 1) b)) 
		(inv_0 a b M K N)
	) 
	(inv_0 |a'| |b'| M K N)
)))

(assert (forall ((a Int) (b Int) (M Int) (K Int) (N Int)) 
(=> 
	(and 
		(= a N) (not (= a b)) 
		(inv_0 a b M K N)
	) 
	false
)))

(check-sat)
