(declare-rel loop ((Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var xx_i Int )
(declare-var xx_i1 Int )
(declare-var xx_i2 Int )
(declare-var xx_i3 Int )
(declare-var xx_i4 Int )
(declare-var xx_i5 Int )
(declare-var xx_i6 Int )
(declare-var xx_i7 Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var xx_array (Array Int Int) )
(declare-var xx_array1 (Array Int Int) )
(declare-var xx_array2 (Array Int Int) )
(declare-var xx_array3 (Array Int Int) )
(declare-var xx_array4 (Array Int Int) )
(declare-var xx_array5 (Array Int Int) )
(declare-var xx_array6 (Array Int Int) )
(declare-var xx_array7 (Array Int Int) )
(declare-var xx_array8 (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
		(> count 0)
	)
	(loop a_array xx_array i count)
))
(rule (=> 
	(and 
		(loop a_array xx_array i count)
		(< i (* count 8))

		(= xx_i (+ (select xx_array (+ i 1)) (select a_array i)))
		(= xx_array1 (store xx_array i xx_i))

		(= xx_i1 (+ (select xx_array1 (+ i 2)) (select a_array (+ i 1))))
		(= xx_array2 (store xx_array1 (+ i 1) xx_i1))

		(= xx_i2 (+ (select xx_array2 (+ i 3)) (select a_array (+ i 2))))
		(= xx_array3 (store xx_array2 (+ i 2) xx_i2))

		(= xx_i3 (+ (select xx_array3 (+ i 4)) (select a_array (+ i 3))))
		(= xx_array4 (store xx_array3 (+ i 3) xx_i3))

		(= xx_i4 (+ (select xx_array4 (+ i 5)) (select a_array (+ i 4))))
		(= xx_array5 (store xx_array4 (+ i 4) xx_i4))

		(= xx_i5 (+ (select xx_array5 (+ i 6)) (select a_array (+ i 5))))
		(= xx_array6 (store xx_array5 (+ i 5) xx_i5))

		(= xx_i6 (+ (select xx_array6 (+ i 7)) (select a_array (+ i 6))))
		(= xx_array7 (store xx_array6 (+ i 6) xx_i6))

		(= xx_i7 (+ (select xx_array7 (+ i 8)) (select a_array (+ i 7))))
		(= xx_array8 (store xx_array7 (+ i 7) xx_i7))
	)
	(loop a_array xx_array8 (+ i 8) count)
))
(rule (=> 
	(and 
		(loop a_array xx_array i count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)