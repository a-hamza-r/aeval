(declare-rel loop ((Array Int Int) (Array Int Int) Int Int ))
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
(declare-var a_i Int )
(declare-var a_i1 Int )
(declare-var a_i2 Int )
(declare-var a_i3 Int )
(declare-var a_i4 Int )
(declare-var a_i5 Int )
(declare-var a_i6 Int )
(declare-var a_i7 Int )
(declare-var a_i_minus_4 Int )
(declare-var a_i_minus_41 Int )
(declare-var a_i_minus_42 Int )
(declare-var a_i_minus_43 Int )
(declare-var a_i_minus_44 Int )
(declare-var a_i_minus_45 Int )
(declare-var a_i_minus_46 Int )
(declare-var a_i_minus_47 Int )
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

		(< 4 (* count 8))
		
		(= a_i (+ (select a_array (- 4 4)) (select b_array 4)))
		(= a_array1 (store a_array 4 a_i))

		(= a_i1 (+ (select a_array1 (- 5 4)) (select b_array 5)))
		(= a_array2 (store a_array1 5 a_i1))

		(= a_i2 (+ (select a_array2 (- 6 4)) (select b_array 6)))
		(= a_array3 (store a_array2 6 a_i2))

		(= a_i3 (+ (select a_array3 (- 7 4)) (select b_array 7)))
		(= a_array4 (store a_array3 7 a_i3))
		
		(= i 8)
	)
	(loop a_array4 b_array i count)
))
(rule (=> 
	(and 
		(loop a_array b_array i count)

		(< i (* count 8))
		
		(= a_i (+ (select a_array (- i 4)) (select b_array i)))
		(= a_array1 (store a_array i a_i))

		(= a_i1 (+ (select a_array1 (- i 3)) (select b_array (+ i 1))))
		(= a_array2 (store a_array1 (+ i 1) a_i1))

		(= a_i2 (+ (select a_array2 (- i 2)) (select b_array (+ i 2))))
		(= a_array3 (store a_array2 (+ i 2) a_i2))

		(= a_i3 (+ (select a_array3 (- i 1)) (select b_array (+ i 3))))
		(= a_array4 (store a_array3 (+ i 3) a_i3))

		(= a_i4 (+ (select a_array4 (- i 0)) (select b_array (+ i 4))))
		(= a_array5 (store a_array4 (+ i 4) a_i4))

		(= a_i5 (+ (select a_array5 (+ i 1)) (select b_array (+ i 5))))
		(= a_array6 (store a_array5 (+ i 5) a_i5))

		(= a_i6 (+ (select a_array6 (+ i 2)) (select b_array (+ i 6))))
		(= a_array7 (store a_array6 (+ i 6) a_i6))

		(= a_i7 (+ (select a_array7 (+ i 3)) (select b_array (+ i 7))))
		(= a_array8 (store a_array7 (+ i 7) a_i7))
	)
	(loop a_array8 b_array (+ i 8) count)
))
(rule (=> 
	(and 
		(loop a_array b_array i count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)