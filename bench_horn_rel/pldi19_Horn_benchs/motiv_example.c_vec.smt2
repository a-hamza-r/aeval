(declare-rel loop ((Array Int Int) (Array Int Int) Int Int))
(declare-rel postLoop ((Array Int Int) (Array Int Int) Int Int))
(declare-rel preLoop ((Array Int Int) (Array Int Int) Int Int))
(declare-rel exit ())
(declare-var b0 Int )
(declare-var i Int )
(declare-var i1 Int )
(declare-var i2 Int )
(declare-var i3 Int )
(declare-var i4 Int )
(declare-var i5 Int )
(declare-var i6 Int )
(declare-var i7 Int )
(declare-var i8 Int )
(declare-var index_limit Int )
(declare-var N Int )
(declare-var a_i Int )
(declare-var a_i1 Int )
(declare-var a_i2 Int )
(declare-var a_i3 Int )
(declare-var a_i4 Int )
(declare-var a_i5 Int )
(declare-var a_i6 Int )
(declare-var a_i7 Int )
(declare-var a_i_prev Int )
(declare-var a_i_prev1 Int )
(declare-var a_i_prev2 Int )
(declare-var a_i_prev3 Int )
(declare-var a_i_prev4 Int )
(declare-var a_i_prev5 Int )
(declare-var a_i_prev6 Int )
(declare-var a_i_prev7 Int )
(declare-var b_i Int )
(declare-var b_i1 Int )
(declare-var b_i2 Int )
(declare-var b_i3 Int )
(declare-var b_i4 Int )
(declare-var b_i5 Int )
(declare-var b_i6 Int )
(declare-var b_i7 Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array1 (Array Int Int) )
(declare-var a_array2 (Array Int Int) )
(declare-var a_array3 (Array Int Int) )
(declare-var a_array4 (Array Int Int) )
(declare-var a_array5 (Array Int Int) )
(declare-var a_array6 (Array Int Int) )
(declare-var a_array7 (Array Int Int) )
(declare-var a_array8 (Array Int Int) )
(declare-var b_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 1)
	)
	(preLoop a_array b_array i count)
))
(rule (=> 
	(and 
		(preLoop a_array b_array i count)
		(< i (- (* count 4) 1))
		
		(= b0 (select b_array 0))

		(= a_i (ite (> b0 0) (+ (select a_array (- i 1)) (select b_array i)) (select a_array i)))
		(= a_array1 (store a_array i a_i))

		(= a_i1 (ite (> b0 0) (+ (select a_array1 i) (select b_array (+ i 1))) (select a_array1 (+ i 1))))
		(= a_array2 (store a_array1 (+ i 1) a_i1))
	)
	(loop a_array2 b_array (+ i 2) count)))
(rule (=> 
	(and 
		(loop a_array b_array i count)

		(< i (- (* count 4) 1))
		(= b0 (select b_array 0))
		
		(= a_i (ite (> b0 0) (+ (select a_array (- i 1)) (select b_array i)) (select a_array i)))
		(= a_array1 (store a_array i a_i))

		(= a_i1 (ite (> b0 0) (+ (select a_array1 i) (select b_array (+ i 1))) (select a_array1 (+ i 1))))
		(= a_array2 (store a_array1 (+ i 1) a_i1))

		(= a_i2 (ite (> b0 0) (+ (select a_array2 (+ i 1)) (select b_array (+ i 2))) (select a_array2 (+ i 2))))
		(= a_array3 (store a_array2 (+ i 2) a_i2))

		(= a_i3 (ite (> b0 0) (+ (select a_array3 (+ i 2)) (select b_array (+ i 3))) (select a_array3 (+ i 3))))
		(= a_array4 (store a_array3 (+ i 3) a_i3))
	)
	(loop a_array4 b_array (+ i 4) count)
))
(rule (=> 
	(and 
		(loop a_array b_array i count)
		
		(= i (- (* count 4) 1))
		(= b0 (select b_array 0))

		(= a_i (ite (> b0 0) (+ (select a_array (- i 1)) (select b_array i)) (select a_array i)))
		(= a_array1 (store a_array i a_i))
	)
	(postLoop a_array1 b_array (+ i 1) count)
))
(rule (=> 
	(and
		(postLoop a_array b_array i count)
		(not (< i (* count 4)))
	)
	exit
))
(query exit)