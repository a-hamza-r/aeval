(declare-rel loop ((Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel exit ())
(declare-var m Int )
(declare-var i Int )
(declare-var a_i Int )
(declare-var b_i Int )
(declare-var c_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array_new (Array Int Int) )
(declare-var b_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
		(= m 1)
		(> count 0)
	)
	(loop a_array b_array i m count)
))
(rule (=> 
	(and 
		(loop a_array b_array i m count)
		(< i (- (* count 8) 1))
		(= a_i (+ (select a_array (+ i m)) (select b_array i)))
		(= a_array_new (store a_array i a_i))
	)
	(loop a_array_new b_array (+ i 1) m count)
))
(rule (=> 
	(and 
		(loop a_array b_array i m count)
		(not (< i (- (* count 8) 1)))
	)
	exit
))
(query exit)