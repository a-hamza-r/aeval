(declare-rel loop ((Array Int Int) (Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var x Int )
(declare-var a_i Int )
(declare-var b_i Int )
(declare-var c_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array1 (Array Int Int) )
(declare-var b_array (Array Int Int) )
(declare-var b_array1 (Array Int Int) )
(declare-var c_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
		(> count 0)
	)
	(loop a_array b_array c_array i count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array i count)
		(< i (* count 8))
		(= a_i (select a_array (- (* count 8) i 1)))
		(= b_i (select b_array i))
		(= c_i (select c_array i))
		(= x (+ (* b_i c_i) a_i))
		(= a_array1 (store a_array i (- x 1)))
		(= b_array1 (store b_array i x))
	)
	(loop a_array1 b_array1 c_array (+ i 1) count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array i count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)