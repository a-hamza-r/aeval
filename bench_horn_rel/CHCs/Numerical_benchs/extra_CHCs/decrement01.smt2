(declare-rel fail ())
(declare-rel init ())
(declare-rel inv (Int ))
(declare-var x Int)
(declare-var y Int)
(declare-var x1 Int)

(rule (=> (and
	(= x 10))
	(inv x)))
(rule (=> (and (inv x)
	(> x 0)
	(= x1 (- x 1)))
	(inv x1)))
(rule (=> (and (inv x)
	(< x 0))
	fail))
(query fail)

; for (int x = 10; x > 0; x++) {}