(declare-rel loop ((Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel preLoop ((Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var alpha Int )
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

		(= a_i1 (+ (select a_array1 (+ i 1)) (* alpha (select b_array (+ i 1)))))
		(= a_array2 (store a_array1 (+ i 1) a_i1))

		(= a_i2 (+ (select a_array2 (+ i 2)) (* alpha (select b_array (+ i 2)))))
		(= a_array3 (store a_array2 (+ i 2) a_i2))

		(= a_i3 (+ (select a_array3 (+ i 3)) (* alpha (select b_array (+ i 3)))))
		(= a_array4 (store a_array3 (+ i 3) a_i3))

		(= a_i4 (+ (select a_array4 (+ i 4)) (* alpha (select b_array (+ i 4)))))
		(= a_array5 (store a_array4 (+ i 4) a_i4))
	)
	(loop a_array4 b_array (+ i 5) alpha count)
))
(rule (=> 
	(and 
		(loop a_array b_array i alpha count)
		(not (< i (- (* count 8) (mod (* count 8) 5))))
	)
	exit
))
(query exit)