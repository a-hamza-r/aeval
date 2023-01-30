(declare-rel loop ((Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var b_i Int )
(declare-var b_i1 Int )
(declare-var b_i2 Int )
(declare-var b_i3 Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var b_array (Array Int Int) )
(declare-var b_array1 (Array Int Int) )
(declare-var b_array2 (Array Int Int) )
(declare-var b_array3 (Array Int Int) )
(declare-var b_array4 (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
		(> count 0)
	)
	(loop a_array b_array i count)
))
(rule (=> 
	(and 
		(loop a_array b_array i count)
		(< i (* count 4))

		(= b_i (+ (select b_array (+ (* count 4) i)) (select a_array i)))
		(= b_array1 (store b_array i b_i))

		(= b_i1 (+ (select b_array1 (+ (* count 4) (+ i 1))) (select a_array (+ i 1))))
		(= b_array2 (store b_array1 (+ i 1) b_i1))

		(= b_i2 (+ (select b_array2 (+ (* count 4) (+ i 2))) (select a_array (+ i 2))))
		(= b_array3 (store b_array2 (+ i 2) b_i2))

		(= b_i3 (+ (select b_array3 (+ (* count 4) (+ i 3))) (select a_array (+ i 3))))
		(= b_array4 (store b_array3 (+ i 3) b_i3))
	)
	(loop a_array b_array4 (+ i 4) count)
))
(rule (=> 
	(and 
		(loop a_array b_array i count)
		(not (< i (* count 4)))
	)
	exit
))
(query exit)