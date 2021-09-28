(declare-rel loop ((Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var alpha Int )
(declare-var a_i Int )
(declare-var b_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array1 (Array Int Int) )
(declare-var b_array (Array Int Int) )
(declare-var c_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
		(> count 0)
		(= alpha (select c_array 0))
	)
	(loop a_array b_array i alpha count)
))
(rule (=> 
	(and 
		(loop a_array b_array i alpha count)
		(< i (- (* count 8) (mod (* count 8) 5)))
		(= a_i (+ (select a_array i) (* alpha (select b_array i))))
		(= a_array1 (store a_array i a_i))
	)
	(loop a_array1 b_array (+ i 1) alpha count)
))
(rule (=> 
	(and 
		(loop a_array b_array i alpha count)
		(not (< i (- (* count 8) (mod (* count 8) 5))))
	)
	exit
))
(query exit)