(declare-rel fail ())
(declare-rel inv1 (Int ))
(declare-rel inv2 (Int ))
(declare-rel inv3 (Int ))
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var x1 Int)
(declare-var y1 Int)
(declare-var z1 Int)

(define-fun psi ((x Int)) Int 
	(- x))

(rule (=> (and
	(= x 0))
	(inv1 x)))
(rule (=> (and (inv1 x)
	(= x1 (+ x 1)))
	(inv1 x1)))
(rule (=> (and (inv1 x)
	(= y (psi x))) 
	(inv2 y)))
(rule (=> (and (inv2 y)
	(= y1 (- y 1)))
	(inv2 y1)))
(rule (=> (and (inv2 y)
	(= z (psi y)))
	(inv3 z)))
(rule (=> (and (inv3 z)
	(= z1 (+ z 1)))
	(inv3 z1)))
(rule (=> (and (inv3 z)
	(< z 0))
	fail))
(query fail)