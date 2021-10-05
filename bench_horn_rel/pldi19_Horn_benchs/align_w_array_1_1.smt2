(declare-rel loop ((Array Int Int) Int Int))
(declare-rel exit ())
(declare-var i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array_new (Array Int Int) )

(rule (=> 
	(and
		(= i 1)
		(> count 0)
	)
	(loop a_array i count)
))
(rule (=> 
	(and 
		(loop a_array i count)
		(< i (* count 8))
		(= a_array_new (store a_array i (+ (select a_array i) 1)))
	)
	(loop a_array_new (+ i 1) count)
))
(rule (=> 
	(and 
		(loop a_array i count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)
