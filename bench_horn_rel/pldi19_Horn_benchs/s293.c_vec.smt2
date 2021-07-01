(declare-rel loop ((Array Int Int) Int Int ))
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
		(> count 0)
	)
	(loop a_array i count)
))
(rule (=> 
	(and 
		(loop a_array i count)

		(< i (* count 8))
		
		(= a_array1 (store a_array i (select a_array 0)))

		(= a_array2 (store a_array1 (+ i 1) (select a_array 0)))

		(= a_array3 (store a_array2 (+ i 2) (select a_array 0)))

		(= a_array4 (store a_array3 (+ i 3) (select a_array 0)))

		(= a_array5 (store a_array4 (+ i 4) (select a_array 0)))

		(= a_array6 (store a_array5 (+ i 5) (select a_array 0)))

		(= a_array7 (store a_array6 (+ i 6) (select a_array 0)))

		(= a_array8 (store a_array7 (+ i 7) (select a_array 0)))
	)
	(loop a_array8 (+ i 8) count)
))
(rule (=> 
	(and 
		(loop a_array i count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)