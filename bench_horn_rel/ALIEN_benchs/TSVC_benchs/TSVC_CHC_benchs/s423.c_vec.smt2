(declare-rel loop ((Array Int Int) (Array Int Int) Int Int ))
(declare-rel preLoop ((Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var array_i Int )
(declare-var array_i1 Int )
(declare-var array_i2 Int )
(declare-var array_i3 Int )
(declare-var array_i4 Int )
(declare-var array_i5 Int )
(declare-var array_i6 Int )
(declare-var array_i7 Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var array (Array Int Int) )
(declare-var array1 (Array Int Int) )
(declare-var array2 (Array Int Int) )
(declare-var array3 (Array Int Int) )
(declare-var array4 (Array Int Int) )
(declare-var array5 (Array Int Int) )
(declare-var array6 (Array Int Int) )
(declare-var array7 (Array Int Int) )
(declare-var array8 (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
		(> count 0)
	)
	(preLoop a_array array i count)
))
(rule (=> 
	(and 
		(preLoop a_array array i count)

		(= array_i (+ (select array (+ i 64)) (select a_array i)))
		(= array1 (store array (+ i 1) array_i))

		(= array_i1 (+ (select array1 (+ i 65)) (select a_array (+ i 1))))
		(= array2 (store array1 (+ i 2) array_i1))

		(= array_i2 (+ (select array2 (+ i 66)) (select a_array (+ i 2))))
		(= array3 (store array2 (+ i 3) array_i2))

		(= array_i3 (+ (select array3 (+ i 67)) (select a_array (+ i 3))))
		(= array4 (store array3 (+ i 4) array_i3))

		(= array_i4 (+ (select array4 (+ i 68)) (select a_array (+ i 4))))
		(= array5 (store array4 (+ i 5) array_i4))

		(= array_i5 (+ (select array5 (+ i 69)) (select a_array (+ i 5))))
		(= array6 (store array5 (+ i 6) array_i5))

		(= array_i6 (+ (select array6 (+ i 70)) (select a_array (+ i 6))))
		(= array7 (store array6 (+ i 7) array_i6))
	)
	(loop a_array array7 (+ i 7) count)
))
(rule (=> 
	(and 
		(loop a_array array i count)
		(< i (- (* count 8) 1))

		(= array_i (+ (select array (+ i 64)) (select a_array i)))
		(= array1 (store array (+ i 1) array_i))

		(= array_i1 (+ (select array1 (+ i 65)) (select a_array (+ i 1))))
		(= array2 (store array1 (+ i 2) array_i1))

		(= array_i2 (+ (select array2 (+ i 66)) (select a_array (+ i 2))))
		(= array3 (store array2 (+ i 3) array_i2))

		(= array_i3 (+ (select array3 (+ i 67)) (select a_array (+ i 3))))
		(= array4 (store array3 (+ i 4) array_i3))

		(= array_i4 (+ (select array4 (+ i 68)) (select a_array (+ i 4))))
		(= array5 (store array4 (+ i 5) array_i4))

		(= array_i5 (+ (select array5 (+ i 69)) (select a_array (+ i 5))))
		(= array6 (store array5 (+ i 6) array_i5))

		(= array_i6 (+ (select array6 (+ i 70)) (select a_array (+ i 6))))
		(= array7 (store array6 (+ i 7) array_i6))

		(= array_i7 (+ (select array7 (+ i 71)) (select a_array (+ i 7))))
		(= array8 (store array7 (+ i 8) array_i7))
	)
	(loop a_array array8 (+ i 8) count)
))
(rule (=> 
	(and 
		(loop a_array array i count)
		(not (< i (- (* count 8) 1)))
	)
	exit
))
(query exit)