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
		(> count 0)
	)
	(loop a_array i sum count)
))
(rule (=> 
	(and 
		(loop a_array i sum count)
		
		(< i (* count 8))
		
		(= a_i (select a_array i))
		(= sum1 (ite (> a_i 0) (+ sum a_i) sum))

		(= a_i1 (select a_array (+ i 1)))
		(= sum2 (ite (> a_i1 0) (+ sum1 a_i1) sum1))

		(= a_i2 (select a_array (+ i 2)))
		(= sum3 (ite (> a_i2 0) (+ sum2 a_i2) sum2))

		(= a_i3 (select a_array (+ i 3)))
		(= sum4 (ite (> a_i3 0) (+ sum3 a_i3) sum3))

		(= a_i4 (select a_array (+ i 4)))
		(= sum5 (ite (> a_i4 0) (+ sum4 a_i4) sum4))

		(= a_i5 (select a_array (+ i 5)))
		(= sum6 (ite (> a_i5 0) (+ sum5 a_i5) sum5))

		(= a_i6 (select a_array (+ i 6)))
		(= sum7 (ite (> a_i6 0) (+ sum6 a_i6) sum6))

		(= a_i7 (select a_array (+ i 7)))
		(= sum8 (ite (> a_i7 0) (+ sum7 a_i7) sum7))
	)
	(loop a_array (+ i 8) sum8 count)
))
(rule (=> 
	(and 
		(loop a_array i sum count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)