(declare-rel fail ())
(declare-rel init ())
(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var c Int)
(declare-var c1 Int)

(rule (=> (and
	(= i 0)
	(= c 1))
	(inv i c)))
(rule (=> (and 
	(inv i c)
	(< i 50)
	(= c1 (* c (+ i 1)))
	(= i1 (+ i 1)))
	(inv i1 c1)))
(rule (=> (and
	(inv i c)
	(>= i 50))
	fail))

(query fail)

; int i = 0, c = 1; 
; for (; i < 50; i++) c*=i+1; 