(declare-rel loop ((Array Int Int) Int Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var t Int )
(declare-var index_limit Int )
(declare-var a_i Int )
(declare-var b_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array_new (Array Int Int) )
(declare-var b_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 1)
		(> count 0)
		(= t (select a_array 0))
		(= a_array_new (store a_array 0 t))
	)
	(loop a_array_new i t count)
))
(rule (=> 
	(and 
		(loop a_array i t count)
		(< i (* count 8))
		(= a_array_new (store a_array i t))
	)
	(loop a_array_new (+ i 1) t count)
))
(rule (=> 
	(and 
		(loop a_array i t count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)