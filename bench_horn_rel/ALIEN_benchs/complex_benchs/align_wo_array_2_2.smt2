(declare-rel loop (Int Int ))
(declare-rel preLoop (Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var count Int )

(rule (=> 
	(and 
		(= i 0)
		(= count 5)
	)
	(preLoop i count)
))
(rule (=> 
	(and 
		(preLoop i count)
	)
	(loop (+ i 1) count)
))
(rule (=> 
	(and 
		(loop i count)
		(< i count)
	)
	(loop (+ i 4) count)
))
(rule (=> 
	(and 
		(loop i count)
		(not (< i count))
	)
	exit
))
(query exit)