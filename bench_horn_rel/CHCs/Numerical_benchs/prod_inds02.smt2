(declare-rel fail ())
(declare-rel init ())
(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var c Int)
(declare-var c1 Int)

(rule (=> (and
	(= i 2)
	(= c 2))
	(inv i c)))
(rule (=> (and 
	(inv i c)
	(< i 48)
	(= c1 (* (* c (+ i 1)) (+ i 2)))
	(= i1 (+ i 2)))
	(inv i1 c1)))
(rule (=> (and
	(inv i c)
	(= i1 (+ i 2))
	(= c1 (* c (* 49 50)))
	(>= i1 50))
	fail))

(query fail)

; int i = 2, c = 2; 
; for (; i < 48; i+=2) c*=(i+1)*(i+2);
; i+=2; c*=49*50 