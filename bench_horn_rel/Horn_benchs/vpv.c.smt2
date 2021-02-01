(declare-rel loop ((Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var i1 Int )
(declare-var index_limit Int )
(declare-var a_i Int )
(declare-var a_i1 Int )
(declare-var b_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array_new (Array Int Int) )
(declare-var b_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
	)
	(loop a_array b_array i count)
))
(rule (=> 
	(and 
		(loop a_array b_array i count)
		(= index_limit (* count 8))
		(< i index_limit)
		(= a_i (select a_array i))
		(= b_i (select b_array i))
		(= a_i1 (+ a_i b_i))
		(= a_array_new (store a_array i a_i1))
		(= i1 (+ i 1))
	)
	(loop a_array_new b_array i1 count)
))
(rule (=> 
	(and 
		(loop a_array b_array i count)
		(= index_limit (* count 8))
		(not (< i index_limit))
	)
	exit
))
(query exit)