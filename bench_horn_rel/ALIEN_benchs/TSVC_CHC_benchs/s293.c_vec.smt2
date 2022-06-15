(declare-rel loop ((Array Int Int) Int Int Int ))
(declare-rel preLoop ((Array Int Int) Int Int Int ))
(declare-rel exit ())
(declare-var t Int )
(declare-var i Int )
(declare-var i1 Int )
(declare-var i2 Int )
(declare-var i3 Int )
(declare-var i4 Int )
(declare-var i5 Int )
(declare-var i6 Int )
(declare-var i7 Int )
(declare-var i8 Int )
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
		(= t (select a_array 0))
		(= a_array1 (store a_array 0 t))
		(= i 1)
		(> count 0)
	)
	(preLoop a_array1 i t count)
))
(rule (=> 
	(and 
		(preLoop a_array i t count)

		(= a_array1 (store a_array i t))

		(= a_array2 (store a_array1 (+ i 1) t))

		(= a_array3 (store a_array2 (+ i 2) t))

		(= a_array4 (store a_array3 (+ i 3) t))

		(= a_array5 (store a_array4 (+ i 4) t))

		(= a_array6 (store a_array5 (+ i 5) t))

		(= a_array7 (store a_array6 (+ i 6) t))
	)
	(loop a_array7 (+ i 7) t count)
))
(rule (=> 
	(and 
		(loop a_array i t count)

		(< i (* count 8))
		
		(= a_array1 (store a_array i t))

		(= a_array2 (store a_array1 (+ i 1) t))

		(= a_array3 (store a_array2 (+ i 2) t))

		(= a_array4 (store a_array3 (+ i 3) t))

		(= a_array5 (store a_array4 (+ i 4) t))

		(= a_array6 (store a_array5 (+ i 5) t))

		(= a_array7 (store a_array6 (+ i 6) t))

		(= a_array8 (store a_array7 (+ i 7) t))
	)
	(loop a_array8 (+ i 8) t count)
))
(rule (=> 
	(and 
		(loop a_array i t count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)