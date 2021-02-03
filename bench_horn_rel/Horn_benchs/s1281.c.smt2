(declare-rel loop ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var i1 Int )
(declare-var x Int )
(declare-var index_limit Int )
(declare-var a_i Int )
(declare-var b_i Int )
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
		(< i (* count 8))
		(= a_i (select a_array i))
		(= b_i (select b_array i))
		(= c_i (select c_array i))
		(= d_i (select d_array i))
		(= e_i (select e_array i))
		(= x (+ (+ (* b_i c_i) (* a_i d_i)) e_i))
		(= a_array_new (store a_array i (- x 1)))
		(= b_array_new (store b_array i x))
	)
	(loop a_array_new b_array_new c_array d_array e_array (+ i 1) count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array e_array i count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)