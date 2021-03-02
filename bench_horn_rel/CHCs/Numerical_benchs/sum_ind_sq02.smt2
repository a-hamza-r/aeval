(declare-rel fail ())
(declare-rel init ())
(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var c Int)
(declare-var c1 Int)

(rule (=> (and
	(= c 14)
	(= i 4))
	(inv i c)))
(rule (=> (and 
	(inv i c)
	(< i 38)
	(= c1 (+ c (* i i)))
	(= i1 (+ i 1)))
	(inv i1 c1)))
(rule (=> (and
	(inv i c)
	(= i1 (+ i 2))
	(= c1 (+ (+ c (* 38 38)) (* 39 39)))
	(>= i1 40))
	fail))

(query fail)

; int i = 4, c = 14; 
; for (; i < 38; i++) c+=i*i; 
; i += 2; c += 38*38+39*39;