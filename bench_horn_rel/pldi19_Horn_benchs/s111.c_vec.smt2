(declare-rel loop ((Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var i1 Int )
(declare-var i2 Int )
(declare-var i3 Int )
(declare-var i4 Int )
(declare-var i_prev Int )
(declare-var i_prev1 Int )
(declare-var i_prev2 Int )
(declare-var i_prev3 Int )
(declare-var index_limit Int )
(declare-var a_i Int )
(declare-var a_i1 Int )
(declare-var a_i2 Int )
(declare-var a_i3 Int )
(declare-var a_i_prev Int )
(declare-var a_i_prev1 Int )
(declare-var a_i_prev2 Int )
(declare-var a_i_prev3 Int )
(declare-var b_i Int )
(declare-var b_i1 Int )
(declare-var b_i2 Int )
(declare-var b_i3 Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array1 (Array Int Int) )
(declare-var a_array2 (Array Int Int) )
(declare-var a_array3 (Array Int Int) )
(declare-var a_array4 (Array Int Int) )
(declare-var b_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 1)
	)
	(loop a_array b_array i count)
))
(rule (=> 
	(and 
		(loop a_array b_array i count)

		(< i (* count 8))
		
		(= a_i (+ (select b_array i) (select a_array (- i 1))))
		(= a_array1 (store a_array i a_i))

		(= a_i1 (+ (select b_array (+ i 2)) (select a_array1 (+ i 1))))
		(= a_array2 (store a_array1 (+ i 2) a_i1))

		(= a_i2 (+ (select b_array (+ i 4)) (select a_array2 (+ i 3))))
		(= a_array3 (store a_array2 (+ i 4) a_i2))

		(= a_i3 (+ (select b_array (+ i 6)) (select a_array3 (+ i 5))))
		(= a_array4 (store a_array3 (+ i 6) a_i3))
	)
	(loop a_array4 b_array (+ i 8) count)
))
(rule (=> 
	(and 
		(loop a_array b_array i count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)