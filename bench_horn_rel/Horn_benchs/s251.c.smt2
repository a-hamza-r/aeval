(declare-rel loop ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var i1 Int )
(declare-var s Int )
(declare-var index_limit Int )
(declare-var a_i Int )
(declare-var b_i Int )
(declare-var c_i Int )
(declare-var d_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array_new (Array Int Int) )
(declare-var b_array (Array Int Int) )
(declare-var c_array (Array Int Int) )
(declare-var d_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
	)
	(loop a_array b_array c_array d_array i count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array i count)
		(< i (* count 8))
		(= b_i (select b_array i))
		(= c_i (select c_array i))
		(= d_i (select d_array i))
		(= s (+ b_i (* c_i d_i)))
		(= a_i (* s s))
		(= a_array_new (store a_array i a_i))
	)
	(loop a_array_new b_array c_array d_array (+ i 1) count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array i count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)