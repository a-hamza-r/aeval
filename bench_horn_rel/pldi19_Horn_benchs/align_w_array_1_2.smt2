(declare-rel loop ((Array Int Int) Int Int))
(declare-rel preLoop ((Array Int Int) Int Int))
(declare-rel postLoop ((Array Int Int) Int Int))
(declare-rel exit ())
(declare-var i Int )
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

(rule (=> 
	(and 
		(= i 1)
		(> count 0)
	)
	(preLoop a_array i count)
))
(rule (=> 
	(and 
		(preLoop a_array i count)
		(= a_array1 (store a_array i (+ (select a_array i) 1)))
	)
	(loop a_array1 (+ i 1) count))
)
(rule (=> 
	(and 
		(loop a_array i count)
		(<= i (- (* count 8) 3))
		(= a_array1 (store a_array i (+ (select a_array i) 1)))
		(= a_array2 (store a_array1 (+ i 1) (+ (select a_array1 (+ i 1)) 1)))
	)
	(loop a_array2 (+ i 2) count)
))
(rule (=> 
	(and 
		(loop a_array i count)
		(>= i (- (* count 8) 2))
		(= a_array1 (store a_array i (+ (select a_array i) 1)))
		(= a_array2 (store a_array1 (+ i 1) (+ (select a_array1 (+ i 1)) 1)))
	)
	(postLoop a_array2 (+ i 2) count)
))
(rule (=> 
	(and
		(postLoop a_array i count)
		(not (<= i (- (* count 8) 1)))
	)
	exit
))
(query exit)