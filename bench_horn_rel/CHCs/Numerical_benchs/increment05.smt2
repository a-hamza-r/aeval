(declare-rel fail ())
(declare-rel init ())
(declare-rel inv (Int Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var limit Int)
(declare-var c Int)
(declare-var c1 Int)

(rule (=> (and
	(= i 0)
	(= c 0)
	(= limit 120))
	(inv i c limit)))
(rule (=> (and 
	(inv i c limit)
	(< i limit)
	(= c1 (+ c 1))
	(= i1 (+ i 1)))
	(inv i1 c1 limit)))

(rule (=> (and
	(inv i c limit)
	(>= i limit))
	fail))

(query fail)

; for (i = 0; i < 120; i++) c++
