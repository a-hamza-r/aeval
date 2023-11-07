(declare-fun inv_0 (Int Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((a Int) (b Int) (M Int) (K Int) (N Int) (c Int) (d Int) (X Int) (Y Int)) 
(=> 
	(and 
		(= a c) (= b d) (= M X) (= K Y) (not (and (not (= a N)) (< a (+ (* 2 M) 1)))) (>= c (+ (* 2 X) 1))
	) 
	(inv_0 a b M K N c d X Y)
)))

(assert (forall ((a Int) (b Int) (M Int) (K Int) (N Int) (c Int) (d Int) (X Int) (Y Int) (|a'| Int) (|b'| Int) (|c'| Int) (|d'| Int)) 
(=> 
	(and 
		(not (= a N)) (= |a'| (+ a 1)) (= |b'| (ite (>= a b) (+ b 1) b)) (not (= c (+ (+ (* 2 X) 1) Y))) (= |c'| (+ c 1)) (= |d'| (+ d 1)) 
		(inv_0 a b M K N c d X Y)
	) 
	(inv_0 |a'| |b'| M K N |c'| |d'| X Y)
)))

(assert (forall ((a Int) (b Int) (M Int) (K Int) (N Int) (c Int) (d Int) (X Int) (Y Int)) 
(=> 
	(and 
		(not (= (not (= a N)) (not (= c (+ (+ (* 2 X) 1) Y))))) 
		(inv_0 a b M K N c d X Y)
	) 
	false
)))

(check-sat)
