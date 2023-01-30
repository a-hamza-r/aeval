(declare-rel loop ((Array Int Int) Int Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var prod Int )
(declare-var prod1 Int )
(declare-var i1 Int )
(declare-var index_limit Int )
(declare-var a_i Int )
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
	)
	(loop a_array (+ i 1) prod1 count)
))
(rule (=> 
	(and 
		(loop a_array i prod count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)