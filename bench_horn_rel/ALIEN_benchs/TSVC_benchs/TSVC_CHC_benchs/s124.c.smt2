(declare-rel loop ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var j Int )
(declare-var mult Int )
(declare-var index_limit Int )
(declare-var a_j Int )
(declare-var b_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array_new (Array Int Int) )
(declare-var b_array (Array Int Int) )
(declare-var c_array (Array Int Int) )
(declare-var d_array (Array Int Int) )
(declare-var e_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
		(> count 0)
	)
	(loop a_array b_array c_array d_array e_array i count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array e_array i count)
		(< i (* count 8))
		(= b_i (select b_array i))
		(= mult (* (select d_array i) (select e_array i)))
		(= a_j (ite (> b_i 0) (+ b_i mult) (+ (select c_array i) mult)))
		(= a_array_new (store a_array i a_j))
	)
	(loop a_array_new b_array c_array d_array e_array (+ i 1) count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array e_array i count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)