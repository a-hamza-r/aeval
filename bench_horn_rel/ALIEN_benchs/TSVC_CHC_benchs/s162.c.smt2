(declare-rel loop ((Array Int Int) (Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var k Int )
(declare-var a_i Int )
(declare-var a_i_plus_k Int )
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
		(> count 0)
		(> k 0)
	)
	(loop a_array b_array c_array i k count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array i k count)
		(< i (- (* count 8) 1))
		(= b_i (select b_array i))
		(= c_i (select c_array i))
		(= a_i_plus_k (select a_array (+ i k)))
		(= a_i (+ a_i_plus_k (* b_i c_i)))
		(= a_array_new (store a_array i a_i))
	)
	(loop a_array_new b_array c_array (+ i 1) k count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array i k count)
		(not (< i (- (* count 8) 1)))
	)
	exit
))
(query exit)