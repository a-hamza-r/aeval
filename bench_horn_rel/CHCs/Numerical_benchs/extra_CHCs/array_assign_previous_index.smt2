(declare-rel exit ())
(declare-rel inv (Int Int (Array Int Int)))
(declare-var i Int)
(declare-var i1 Int)
(declare-var a_i Int)
(declare-var limit Int)
(declare-var array (Array Int Int))
(declare-var arrayy (Array Int Int))
(declare-var arrayy1 (Array Int Int))
(declare-var array1 (Array Int Int))

(rule (=> 
	(and 
		(= i 0)
		(>= limit 0)
	)
	(inv i limit array))
)

(rule (=> 
	(and
		(inv i limit array)
		(< i limit)
		(= i1 (+ i 1))
		(= a_i (select array (- i 1)))
		(= array1 (store array i a_i))
	)
	(inv i1 limit array1)
))

(rule (=> 
	(and
		(inv i limit array)
		(>= i limit)
		(and
			(> i1 0)
			(< i1 limit)
			(not (= (select array i1) (select array (- i1 1))))
		)
	)
	exit
))

(query exit)