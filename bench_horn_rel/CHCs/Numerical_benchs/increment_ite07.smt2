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
	(= limit 60))
	(inv i c limit)))
(rule (=> (and 
	(inv i c limit)
	(< i limit)
	(= c1 (ite (< i 20) (+ c 1) (ite (< i 40) (+ c 2) (ite (< i 60) (+ c 3)))))
	(= i1 (+ i 1)))
	(inv i1 c1 limit)))
(rule (=> (and
	(inv i c limit)
	(>= i 60))
	fail))

(query fail)

; for (i = 0; i < 60; i++) {if (i < 20) c++; else if (i < 40) c = c + 2; else c = c + 3;}


