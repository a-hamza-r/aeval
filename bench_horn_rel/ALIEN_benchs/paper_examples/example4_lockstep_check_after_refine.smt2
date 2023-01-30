(declare-fun inv_0 (Int Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((a Int) (b Int) (M Int) (K Int) (N Int) (c Int) (d Int) (X Int) (Y Int)) 
(=> 
	(and 
		(= a c) (= b d) (= M X) (= K Y) (or (= a N) (>= a (+ (* 2 M) 1))) (>= c (+ (* 2 X) 1))
		(> (* 2 M) (- 1)) (>= K 0) (>= (+ b Y (* (- 2) M) (* (- 1) K)) 1) (>= (+ K (* 2 M) (* (- 1) b) (* (- 1) Y)) (- 1)) (>= (+ Y (* 2 M) (* (- 1) N)) (- 1)) (>= (+ N Y (* (- 2) M) (* (- 2) K)) 1) (>= (+ a d (* (- 1) b) (* (- 1) c)) 0) (>= (+ b c (* (- 1) d) (* (- 1) a)) 0) (>= (+ a X (* (- 1) c) (* (- 1) M)) 0) (>= (+ M c (* (- 1) X) (* (- 1) a)) 0) (>= (+ a K (* (- 1) c) (* (- 1) Y)) 0) (>= (+ K c (* (- 1) Y) (* (- 1) a)) 0) (>= (+ c (* 2 M) (* (- 1) N) (* (- 1) Y) (* 2 K)) 0) (>= (mod a 2) 1)
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
