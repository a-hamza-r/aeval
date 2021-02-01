(declare-rel loop ((Array Int Int) (Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var i1 Int )
(declare-var index_limit Int )
(declare-var a_i Int )
(declare-var b_i Int )
(declare-var c_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array_new (Array Int Int) )
(declare-var b_array (Array Int Int) )
(declare-var c_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
	)
	(loop a_array b_array c_array i count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array i count)
		(= index_limit (* count 8))
		(< i index_limit)
		(= b_i (select b_array i))
		(= c_i (select c_array i))
		(= a_i (+ b_i (* c_i (+ i 1))))
		(= a_array_new (store a_array i a_i))
		(= i1 (+ i 1))
	)
	(loop a_array_new b_array c_array i1 count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array i count)
		(not (< i index_limit))
		;(<= 0 i1)
		;(< i1 index_limit)
		;(not (< (select b_array i1) (select a_array i1)))
	)
	exit
))
(query exit)