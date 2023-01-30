(declare-rel loop ((Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var xx_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var xx_array (Array Int Int) )
(declare-var xx_array1 (Array Int Int) )

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
	)
	(loop a_array xx_array1 (+ i 1) count)
))
(rule (=> 
	(and 
		(loop a_array xx_array i count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)