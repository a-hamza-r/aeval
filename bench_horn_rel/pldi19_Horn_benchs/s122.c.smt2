(declare-rel loop ((Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var i1 Int )
(declare-var k Int )
(declare-var k1 Int )
(declare-var index_limit Int )
(declare-var a_i Int )
(declare-var a_i_curr Int )
(declare-var b_elem Int )
(declare-var b_ind Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array_new (Array Int Int) )
(declare-var b_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 1)
		(= k 0)
	)
	(loop a_array b_array i k count)
))
(rule (=> 
	(and 
		(loop a_array b_array i k count)
		(< i (* count 8))
		(= a_i (+ (select b_array (- (* count 8) (+ k 1))) (select a_array i)))
		(= a_array_new (store a_array i a_i))
	)
	(loop a_array_new b_array (+ i 1) (+ k 1) count)
))
(rule (=> 
	(and 
		(loop a_array b_array i k count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)