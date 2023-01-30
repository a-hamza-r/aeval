(declare-rel loop ((Array Int Int) Int Int Int ))
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
(declare-var prod Int )
(declare-var prod1 Int )
(declare-var prod2 Int )
(declare-var prod3 Int )
(declare-var prod4 Int )
(declare-var prod5 Int )
(declare-var prod6 Int )
(declare-var prod7 Int )
(declare-var prod8 Int )
(declare-var index_limit Int )
(declare-var a_i Int )
(declare-var a_i1 Int )
(declare-var a_i2 Int )
(declare-var a_i3 Int )
(declare-var a_i4 Int )
(declare-var a_i5 Int )
(declare-var a_i6 Int )
(declare-var a_i7 Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
		(= prod 0)
		(> count 0)
	)
	(loop a_array i prod count)
))
(rule (=> 
	(and 
		(loop a_array i prod count)
		
		(< i (* count 8))
		
		(= a_i (select a_array i))
		(= prod1 (* prod a_i))

		(= a_i1 (select a_array (+ i 1)))
		(= prod2 (* prod1 a_i1))

		(= a_i2 (select a_array (+ i 2)))
		(= prod3 (* prod2 a_i2))

		(= a_i3 (select a_array (+ i 3)))
		(= prod4 (* prod3 a_i3))

		(= a_i4 (select a_array (+ i 4)))
		(= prod5 (* prod4 a_i4))

		(= a_i5 (select a_array (+ i 5)))
		(= prod6 (* prod5 a_i5))

		(= a_i6 (select a_array (+ i 6)))
		(= prod7 (* prod6 a_i6))

		(= a_i7 (select a_array (+ i 7)))
		(= prod8 (* prod7 a_i7))
	)
	(loop a_array (+ i 8) prod8 count)
))
(rule (=> 
	(and 
		(loop a_array i prod count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)