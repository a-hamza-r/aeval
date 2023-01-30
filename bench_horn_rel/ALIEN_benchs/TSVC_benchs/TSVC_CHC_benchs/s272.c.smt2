(declare-rel loop ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var t Int )
(declare-var i1 Int )
(declare-var a_i Int )
(declare-var b_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array_new (Array Int Int) )
(declare-var b_array (Array Int Int) )
(declare-var b_array_new (Array Int Int) )
(declare-var c_array (Array Int Int) )
(declare-var d_array (Array Int Int) )
(declare-var e_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
		(> count 0)
	)
	(loop a_array b_array c_array d_array e_array i t count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array e_array i t count)
		(< i (* count 8))
		(= a_i (ite (>= (select e_array i) t) (+ (select a_array i) (* (select c_array i) (select d_array i))) (select a_array i)))
		(= b_i (ite (>= (select e_array i) t) (+ (select b_array i) (* (select c_array i) (select c_array i))) (select b_array i)))
		(= a_array_new (store a_array i a_i))
		(= b_array_new (store b_array i b_i))
	)
	(loop a_array_new b_array_new c_array d_array e_array (+ i 1) t count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array e_array i t count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)