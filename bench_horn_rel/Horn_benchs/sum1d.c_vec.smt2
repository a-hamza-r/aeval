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
(declare-var sum Int )
(declare-var sum1 Int )
(declare-var sum2 Int )
(declare-var sum3 Int )
(declare-var sum4 Int )
(declare-var sum5 Int )
(declare-var sum6 Int )
(declare-var sum7 Int )
(declare-var sum8 Int )
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
		(= sum 0)
	)
	(loop a_array i sum count)
))
(rule (=> 
	(and 
		(loop a_array i sum count)
		
		(= index_limit (* count 8))
		(< i index_limit)
		
		(= a_i (select a_array i))
		(= sum1 (+ sum a_i))
		(= i1 (+ i 1))

		(= a_i1 (select a_array i1))
		(= sum2 (+ sum1 a_i1))
		(= i2 (+ i1 1))

		(= a_i2 (select a_array i2))
		(= sum3 (+ sum2 a_i2))
		(= i3 (+ i2 1))

		(= a_i3 (select a_array i3))
		(= sum4 (+ sum3 a_i3))
		(= i4 (+ i3 1))

		(= a_i4 (select a_array i4))
		(= sum5 (+ sum4 a_i4))
		(= i5 (+ i4 1))

		(= a_i5 (select a_array i5))
		(= sum6 (+ sum5 a_i5))
		(= i6 (+ i5 1))

		(= a_i6 (select a_array i6))
		(= sum7 (+ sum6 a_i6))
		(= i7 (+ i6 1))

		(= a_i7 (select a_array i7))
		(= sum8 (+ sum7 a_i7))
		(= i8 (+ i7 1))
	)
	(loop a_array i8 sum8 count)
))
(rule (=> 
	(and 
		(loop a_array i sum count)
		(= index_limit (* count 8))
		(not (< i index_limit))
	)
	exit
))
(query exit)