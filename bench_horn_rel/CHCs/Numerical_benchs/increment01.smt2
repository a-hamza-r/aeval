(declare-rel fail ())
(declare-rel init ())
(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var c Int)
(declare-var c1 Int)

(rule (=> (and
	(= i 0)
	(= c 0))
	(inv i c)))
(rule (=> (and 
	(inv i c)
	(< i 40)
	(= c1 (+ c 1))
	(= i1 (+ i 1)))
	(inv i1 c1)))

(rule (=> (and
	(inv i c)
	(>= i 40))
	fail))

(query fail)

; for (i = 0; i < 40; i++) c++
