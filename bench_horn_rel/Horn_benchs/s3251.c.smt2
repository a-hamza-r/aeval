(declare-rel loop ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var i1 Int )
(declare-var index_limit Int )
(declare-var a_i Int )
(declare-var a_i_plus_1 Int )
(declare-var b_i Int )
(declare-var b_i_new Int )
(declare-var c_i Int )
(declare-var d_i Int )
(declare-var e_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array_new (Array Int Int) )
(declare-var b_array (Array Int Int) )
(declare-var b_array_new (Array Int Int) )
(declare-var c_array (Array Int Int) )
(declare-var d_array (Array Int Int) )
(declare-var d_array_new (Array Int Int) )
(declare-var e_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
	)
	(loop a_array b_array c_array d_array e_array i count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array e_array i count)
		(< i (- (* count 8) 1))
		(= a_i (select a_array i))
		(= b_i (select b_array i))
		(= c_i (select c_array i))
		(= e_i (select e_array i))
		(= a_i_plus_1 (+ b_i c_i))
		(= a_array_new (store a_array (+ i 1) a_i_plus_1))
		(= b_i_new (* c_i e_i))
		(= b_array_new (store b_array i b_i_new))
		(= d_i (* a_i e_i))
		(= d_array_new (store d_array i d_i))
	)
	(loop a_array_new b_array_new c_array d_array_new e_array (+ i 1) count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array e_array i count)
		(not (< i (- (* count 8) 1)))
	)
	exit
))
(query exit)