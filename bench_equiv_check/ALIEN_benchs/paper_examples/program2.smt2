(declare-fun inv_0 (Int Int Int Int) Bool)
(declare-fun inv_1 (Int Int Int Int) Bool)

(assert (forall ((c Int) (d Int) (X Int) (Y Int)) 
(=> 
	(and 
		(= c 1) (= d (+ (* 2 X) 1)) (>= X 0) (>= Y 0)
	) 
	(inv_0 c d X Y)
)))

(assert (forall ((c Int) (d Int) (X Int) (Y Int) (|c'| Int)) 
(=> 
	(and 
		(< c (+ (* 2 X) 1)) (= |c'| (+ c 2)) 
		(inv_0 c d X Y)
	) 
	(inv_0 |c'| d X Y)
)))

(assert (forall ((c Int) (d Int) (X Int) (Y Int)) 
(=> 
	(and 
		(not (< c (+ (* 2 X) 1))) 
		(inv_0 c d X Y)
	) 
	(inv_1 c d X Y)
)))

(assert (forall ((c Int) (d Int) (X Int) (Y Int) (|c'| Int) (|d'| Int)) 
(=> 
	(and 
		(not (= c (+ (+ (* 2 X) 1) Y))) (= |c'| (+ c 1)) (= |d'| (+ d 1)) 
		(inv_1 c d X Y)
	) 
	(inv_1 |c'| |d'| X Y)
)))

(assert (forall ((c Int) (d Int) (X Int) (Y Int)) 
(=> 
	(and 
		(= c (+ (+ (* 2 X) 1) Y)) (not (= c d)) 
		(inv_1 c d X Y)
	) 
	false
)))

(check-sat)
