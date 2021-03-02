(declare-rel inv (Int Int Int Int Int))
(declare-var k0 Int)
(declare-var k1 Int)
(declare-var k2 Int)
(declare-var i0 Int)
(declare-var i1 Int)
(declare-var j0 Int)
(declare-var j1 Int)
(declare-var n0 Int)
(declare-var n1 Int)
(declare-var b0 Int)
(declare-var b1 Int)
(declare-var nondet0 Int)

(declare-rel fail ())

(rule (=> 
	(and
		(= k1 (ite (< k0 0) (* (- 1) k0) k0))
		(= i0 k1)
		(= j0 k1)
		(= n0 0)
		(= b0 (ite (= nondet0 0) 1 0))
	)
	(inv k1 i0 j0 n0 b0)
	)
)

(rule (=> 
	(and
	    (inv k1 i0 j0 n0 b0)
	    (= i1 (ite (= b0 0) (+ i0 1) i0))
	    (= b1 (ite (= b0 0) 1 0))
	    (= j1 (ite (= b0 0) j0 (+ j0 1)))
	    (= k2 (+ k1 1))
	    (= n1 (ite (or (> i1 k2) (> j1 k2)) (- n0 1) (+ n0 (+ i1 j1))))
	)
	(inv k2 i1 j1 n1 b1)
	)
)


(rule (=> (and (inv k1 i0 j0 n0 b0)
   (not (>= n0 0))) fail))

(query fail)
