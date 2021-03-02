(declare-var i Int )
(declare-var i1 Int )
(declare-var len Int )
(declare-var array (Array Int Int))
(declare-var array1 (Array Int Int))
(declare-rel loop (Int (Array Int Int) Int))
(declare-rel exit ())

(rule (=> 
	(and 
		(= i 0)
		(>= len 0)
	)
	(loop i array len)
))

(rule (=> 
	(and 
		(loop i array len)
		(= array1 (store array i (- i)))
		(= i1 (+ i 1))
		(< i len)
	)
	(loop i1 array1 len)
))

(rule (=> 
	(and 
		(loop i array len)
		(>= i len)
		(>= i1 0)
		(< i1 len)
		(not (= (select array i1) (- i1)))
	)
	exit
))

(query exit)