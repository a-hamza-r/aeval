(declare-rel loop ((Array Int Int) (Array Int (Array Int Int)) (Array Int Int) Int Int Int Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var j Int )
(declare-var inc Int )
(declare-var sum Int )
(declare-var sum1 Int )
(declare-var i1 Int )
(declare-var count Int )
(declare-var a (Array Int Int) )
(declare-var ip (Array Int Int) )
(declare-var aa (Array Int (Array Int Int)) )
(declare-var a1 (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
		(= sum 0)
		(> count 0)
	)
	(loop a aa ip i j inc sum count)
))
(rule (=> 
	(and 
		(loop a aa ip i j inc sum count)
		(< i (- (* count 8) 1))
		(= sum1 (+ sum (* (select a (+ inc i)) (select (select aa (- j 1)) (select ip i)))))
		(= i1 (+ i 1))
	)
	(loop a aa ip i1 j inc sum1 count)
))
(rule (=> 
	(and 
		(loop a aa ip i j inc sum count)
		(not (< i (- (* count 8) 1)))
	)
	exit
))
(query exit)