(declare-rel fail ())
(declare-rel init ())
(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var c Int)
(declare-var c1 Int)

(rule (=> (and
	(= c 0)
	(= i 0))
	(inv i c)))
(rule (=> (and 
	(inv i c)
	(< i 40)
	(= c1 (+ c i))
	(= i1 (+ i 1)))
	(inv i1 c1)))
(rule (=> (and
	(inv i c)
	(>= i 40))
	fail))

(query fail)

; int i = 0, c = 0; 
; for (; i < 40; i++) c+=i; 