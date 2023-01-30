(declare-rel loop ((Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var array_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var array (Array Int Int) )
(declare-var array1 (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
		(> count 0)
	)
	(loop a_array array i count)
))
(rule (=> 
	(and 
		(loop a_array array i count)
		(< i (- (* count 8) 1))
		(= array_i (+ (select array i) (select a_array i)))
		(= array1 (store array (+ i 64) array_i))
	)
	(loop a_array array1 (+ i 1) count)
))
(rule (=> 
	(and 
		(loop a_array array i count)
		(not (< i (- (* count 8) 1)))
	)
	exit
))
(query exit)