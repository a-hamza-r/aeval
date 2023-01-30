(declare-rel loop ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var mid Int )
(declare-var i1 Int )
(declare-var a_i Int )
(declare-var b_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array1 (Array Int Int) )
(declare-var b_array (Array Int Int) )
(declare-var c_array (Array Int Int) )
(declare-var d_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
		(> count 0)
	)
	(loop a_array b_array c_array d_array i mid count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array i mid count)
		(< i (* count 8))
		(= a_i (ite (< (+ i 1) mid) (+ (select a_array i) (* (select b_array i) (select c_array i))) (+ (select a_array i) (* (select b_array i) (select d_array i)))))
		(= a_array1 (store a_array i a_i))
	)
	(loop a_array1 b_array c_array d_array (+ i 1) mid count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array i mid count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)