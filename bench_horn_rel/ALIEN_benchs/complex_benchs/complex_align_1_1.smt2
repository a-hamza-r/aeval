(declare-rel loop (Int Int Int))
(declare-rel postLoop (Int Int Int))
(declare-rel preLoop (Int Int Int))
(declare-rel exit ())
(declare-var b0 Int )
(declare-var i Int )
(declare-var x Int )
(declare-var x1 Int )
(declare-var x2 Int )
(declare-var x3 Int )
(declare-var x4 Int )
(declare-var x5 Int )
(declare-var x6 Int )
(declare-var i1 Int )
(declare-var a_i Int )
(declare-var a_i1 Int )
(declare-var a_i2 Int )
(declare-var count Int )

(rule (=> 
	(and
		(= i 0)
		(> count 0)
	)
	(preLoop x i count)
))
(rule (=>
	(and
		(preLoop x i count)
		(= x1 (+ (+ x 0) 1))
	)
	(loop x1 (+ i 2) count)
))
(rule (=> 
	(and 
		(loop x i count)
		(< i (* count 6))
		
		(= x1 (+ x (* i i)))
		(= x2 (+ x1 (* (+ i 1) (+ i 1))))
	)
	(loop x2 (+ i 2) count)
))
(rule (=> 
	(and 
		(loop x i count)
		(not (< i (* count 6)))
	)
	exit
))
(query exit)
