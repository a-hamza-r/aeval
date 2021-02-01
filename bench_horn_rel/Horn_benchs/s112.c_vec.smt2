(declare-rel loop ((Array Int Int) (Array Int Int) Int Int))
(declare-rel exit ())
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
		(= i (- (* count 8) 1))
		(>= i 1)

		(= b_i (select b_array i))
		(= a_i_prev (select a_array (- i 1)))
		(= a_i (+ a_i_prev b_i))
		(= a_array1 (store a_array i a_i))
		(= i1 (- i 1))

		(= b_i1 (select b_array i1))
		(= a_i_prev1 (select a_array1 (- i1 1)))
		(= a_i1 (+ a_i_prev1 b_i1))
		(= a_array2 (store a_array1 i1 a_i1))
		(= i2 (- i1 1))

		(= b_i2 (select b_array i2))
		(= a_i_prev2 (select a_array2 (- i2 1)))
		(= a_i2 (+ a_i_prev2 b_i2))
		(= a_array3 (store a_array2 i2 a_i2))
		(= i3 (- i2 1))

		(= b_i3 (select b_array i3))
		(= a_i_prev3 (select a_array3 (- i3 1)))
		(= a_i3 (+ a_i_prev3 b_i3))
		(= a_array4 (store a_array3 i3 a_i3))
		(= i4 (- i3 1))

		(= b_i4 (select b_array i4))
		(= a_i_prev4 (select a_array4 (- i4 1)))
		(= a_i4 (+ a_i_prev4 b_i4))
		(= a_array5 (store a_array4 i4 a_i4))
		(= i5 (- i4 1))

		(= b_i5 (select b_array i5))
		(= a_i_prev5 (select a_array5 (- i5 1)))
		(= a_i5 (+ a_i_prev5 b_i5))
		(= a_array6 (store a_array5 i5 a_i5))
		(= i6 (- i5 1))

		(= b_i6 (select b_array i6))
		(= a_i_prev6 (select a_array6 (- i6 1)))
		(= a_i6 (+ a_i_prev6 b_i6))
		(= a_array7 (store a_array6 i6 a_i6))
		(= i7 (- i6 1))
	)
	(loop a_array7 b_array i7 count)
))
(rule (=> 
	(and 
		(loop a_array b_array i count)

		(>= i 1)
		
		(= b_i (select b_array i))
		(= a_i_prev (select a_array (- i 1)))
		(= a_i (+ a_i_prev b_i))
		(= a_array1 (store a_array i a_i))
		(= i1 (- i 1))

		(= b_i1 (select b_array i1))
		(= a_i_prev1 (select a_array1 (- i1 1)))
		(= a_i1 (+ a_i_prev1 b_i1))
		(= a_array2 (store a_array1 i1 a_i1))
		(= i2 (- i1 1))

		(= b_i2 (select b_array i2))
		(= a_i_prev2 (select a_array2 (- i2 1)))
		(= a_i2 (+ a_i_prev2 b_i2))
		(= a_array3 (store a_array2 i2 a_i2))
		(= i3 (- i2 1))

		(= b_i3 (select b_array i3))
		(= a_i_prev3 (select a_array3 (- i3 1)))
		(= a_i3 (+ a_i_prev3 b_i3))
		(= a_array4 (store a_array3 i3 a_i3))
		(= i4 (- i3 1))

		(= b_i4 (select b_array i4))
		(= a_i_prev4 (select a_array4 (- i4 1)))
		(= a_i4 (+ a_i_prev4 b_i4))
		(= a_array5 (store a_array4 i4 a_i4))
		(= i5 (- i4 1))

		(= b_i5 (select b_array i5))
		(= a_i_prev5 (select a_array5 (- i5 1)))
		(= a_i5 (+ a_i_prev5 b_i5))
		(= a_array6 (store a_array5 i5 a_i5))
		(= i6 (- i5 1))

		(= b_i6 (select b_array i6))
		(= a_i_prev6 (select a_array6 (- i6 1)))
		(= a_i6 (+ a_i_prev6 b_i6))
		(= a_array7 (store a_array6 i6 a_i6))
		(= i7 (- i6 1))

		(= b_i7 (select b_array i7))
		(= a_i_prev7 (select a_array7 (- i7 1)))
		(= a_i7 (+ a_i_prev7 b_i7))
		(= a_array8 (store a_array7 i7 a_i7))
		(= i8 (- i7 1))
	)
	(loop a_array8 b_array i8 count)
))
(rule (=> 
	(and 
		(loop a_array b_array i count)
		(not (>= i 1))
	)
	exit
))
(query exit)