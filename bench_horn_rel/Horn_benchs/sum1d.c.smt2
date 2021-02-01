(declare-rel loop ((Array Int Int) Int Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var sum Int )
(declare-var sum1 Int )
(declare-var i1 Int )
(declare-var index_limit Int )
(declare-var a_i Int )
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
		(loop a_array sum i count)
		(= index_limit (* count 8))
		(< i index_limit)
		(= a_i (select a_array i))
		(= sum1 (+ sum a_i))
		(= i1 (+ i 1))
	)
	(loop a_array sum1 i1 count)
))
(rule (=> 
	(and 
		(loop a_array sum i count)
		(not (< i index_limit))
	)
	exit
))
(query exit)