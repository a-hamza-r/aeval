(declare-rel loop ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var i1 Int )
(declare-var a_i Int )
(declare-var a_i1 Int )
(declare-var b_i Int )
(declare-var c_i Int )
(declare-var d_i Int )
(declare-var ip_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array1 (Array Int Int) )
(declare-var b_array (Array Int Int) )
(declare-var c_array (Array Int Int) )
(declare-var d_array (Array Int Int) )
(declare-var ip_array (Array Int Int) )


(rule (=> 
	(and 
		(= i 0)
		(> count 0)
	)
	(loop a_array b_array c_array d_array ip_array i count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array ip_array i count)
		(< i (* count 8))
		(= c_i (select c_array i))
		(= d_i (select d_array i))
		(= b_i (select b_array i))
		(= ip_i (select ip_array i))
		(= a_i (+ b_i (* c_i d_i)))
		(= a_array1 (store a_array ip_i a_i))
	)
	(loop a_array1 b_array c_array d_array ip_array (+ i 1) count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array ip_array i count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)