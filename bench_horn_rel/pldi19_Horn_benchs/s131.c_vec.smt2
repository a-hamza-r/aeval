(declare-rel loop ((Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel preLoop ((Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel exit ())
(declare-var m Int )
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
		(= i 0)
		(= m 1)
		(> count 0)
	)
	(preLoop a_array b_array i m count)
))
(rule (=> 
	(and 
		(preLoop a_array b_array i m count)

		(= a_i (+ (select a_array (+ i m)) (select b_array i)))
		(= a_array1 (store a_array i a_i))

		(= a_i1 (+ (select a_array1 (+ (+ i 1) m)) (select b_array (+ i 1))))
		(= a_array2 (store a_array1 (+ i 1) a_i1))

		(= a_i2 (+ (select a_array2 (+ (+ i 2) m)) (select b_array (+ i 2))))
		(= a_array3 (store a_array2 (+ i 2) a_i2))

		(= a_i3 (+ (select a_array3 (+ (+ i 3) m)) (select b_array (+ i 3))))
		(= a_array4 (store a_array3 (+ i 3) a_i3))

		(= a_i4 (+ (select a_array4 (+ (+ i 4) m)) (select b_array (+ i 4))))
		(= a_array5 (store a_array4 (+ i 4) a_i4))

		(= a_i5 (+ (select a_array5 (+ (+ i 5) m)) (select b_array (+ i 5))))
		(= a_array6 (store a_array5 (+ i 5) a_i5))

		(= a_i6 (+ (select a_array6 (+ (+ i 6) m)) (select b_array (+ i 6))))
		(= a_array7 (store a_array6 (+ i 6) a_i6))
	)
	(loop a_array7 b_array (+ i 7) m count)
))
(rule (=> 
	(and 
		(loop a_array b_array i m count)
		
		(< i (- (* count 8) 1))
		
		(= a_i (+ (select a_array (+ i m)) (select b_array i)))
		(= a_array1 (store a_array i a_i))

		(= a_i1 (+ (select a_array1 (+ (+ i 1) m)) (select b_array (+ i 1))))
		(= a_array2 (store a_array1 (+ i 1) a_i1))

		(= a_i2 (+ (select a_array2 (+ (+ i 2) m)) (select b_array (+ i 2))))
		(= a_array3 (store a_array2 (+ i 2) a_i2))

		(= a_i3 (+ (select a_array3 (+ (+ i 3) m)) (select b_array (+ i 3))))
		(= a_array4 (store a_array3 (+ i 3) a_i3))

		(= a_i4 (+ (select a_array4 (+ (+ i 4) m)) (select b_array (+ i 4))))
		(= a_array5 (store a_array4 (+ i 4) a_i4))

		(= a_i5 (+ (select a_array5 (+ (+ i 5) m)) (select b_array (+ i 5))))
		(= a_array6 (store a_array5 (+ i 5) a_i5))

		(= a_i6 (+ (select a_array6 (+ (+ i 6) m)) (select b_array (+ i 6))))
		(= a_array7 (store a_array6 (+ i 6) a_i6))

		(= a_i7 (+ (select a_array7 (+ (+ i 7) m)) (select b_array (+ i 7))))
		(= a_array8 (store a_array7 (+ i 7) a_i7))
	)
	(loop a_array8 b_array (+ i 8) m count)
))
(rule (=> 
	(and 
		(loop a_array b_array i m count)
		(not (< i (- (* count 8) 1)))
	)
	exit
))
(query exit)