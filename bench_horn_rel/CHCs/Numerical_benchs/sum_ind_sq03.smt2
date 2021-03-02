(declare-rel fail ())
(declare-rel init ())
(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var c Int)
(declare-var c1 Int)

(rule (=> (and
	(= c 75)
	(= i 6))
	(inv i c)))
(rule (=> (and 
	(inv i c)
	(< i 34)
	(= c1 (+ c (* i i)))
	(= i1 (+ i 1)))
	(inv i1 c1)))
(rule (=> (and
	(inv i c)
	(= i1 (+ i 6))
	(= c1 (+ (+ (+ (+ (+ (+ c (* 34 34)) (* 35 35)) (* 36 36)) (* 37 37)) (* 38 38)) (* 39 39))) 
	(>= i1 40))
	fail))

(query fail)

; int i = 6, c = 75; 
; for (; i < 34; i++) c+=i*i; 
; i += 6; c += 34*34+35*35+36*36+37*37+38*38+39*39;