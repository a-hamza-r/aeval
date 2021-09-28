(declare-rel loop (Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var count Int )

(rule (=> 
	(and 
		(= i 0)
		(= count 5)
	)
	(loop i count)
))
(rule (=> 
	(and 
		(loop i count)
		(< i count)
	)
	(loop (+ i 1) count)
))
(rule (=> 
	(and 
		(loop i count)
		(not (< i count))
	)
	exit
))
(query exit)