(declare-rel fail ())
(declare-rel init ())
(declare-rel inv (Int Int Int Int))
(declare-var v1_i Int)
(declare-var v1_i1 Int)
(declare-var v1_c Int)
(declare-var v1_c1 Int)
(declare-var v2_i Int)
(declare-var v2_i1 Int)
(declare-var v2_c Int)
(declare-var v2_c1 Int)

(rule (=> (and
	(= v1_i 0)
	(= v1_c 0)
	(= v2_i 0)
	(= v2_c 0))
	(inv v1_i v1_c v2_i v2_c)))
(rule (=> (and 
	(inv v1_i v1_c v2_i v2_c)
	(< v1_i 30)
	(= v1_c1 (+ v1_c 1))
	(= v1_i1 (+ v1_i 1))
	(< v2_i 20)
	(= v2_c1 (ite (= (mod v2_i 2) 0) (+ v2_c 1) (+ v2_c 2)))
	(= v2_i1 (+ v2_i 1)))
	(inv v1_i1 v1_c1 v2_i1 v2_c1)))

(rule (=> (and
	(inv v1_i v1_c v2_i v2_c)
	(>= v1_i 30)
	(>= v2_i 20))
	fail))

(query fail)

; Product of: 
; for (i = 0; i < 30; i++) c++
; for (i = 0; i < 20; i++) {if (i mod 2 == 0) c++; else c = c + 2}