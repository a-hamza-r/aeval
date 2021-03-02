(declare-rel fail ())
(declare-rel init ())
(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var c Int)
(declare-var c1 Int)

(rule (=> (and
	(= c 3)
	(= i 3))
	(inv i c)))
(rule (=> (and 
	(inv i c)
	(< i 36)
	(= c1 (+ c i))
	(= i1 (+ i 1)))
	(inv i1 c1)))
(rule (=> (and
	(inv i c)
	(= i1 (+ i 4))
	(= c1 (+ (+ (+ (+ c 36) 37) 38) 39))
	(>= i1 40))
	fail))

(query fail)

; int i = 3, c = 3; 
; for (; i < 36; i++) c+=i; 
; i += 4; c += 36+37+38+39;