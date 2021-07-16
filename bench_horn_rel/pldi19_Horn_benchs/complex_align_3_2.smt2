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
		(= x1 (+ (+ (+ x 0) 1) 2))
	)
	(loop x1 (+ i 3) count)
))
(rule (=> 
	(and 
		(loop x i count)
		(< i (- (* count 6) 6))
		
		(= x1 (+ x i))
		(= x2 (+ x1 (+ i 1)))
		(= x3 (+ x2 (+ i 2)))
	)
	(loop x3 (+ i 3) count)
))
(rule (=> 
	(and
		(loop x i count)
		(= i (- (* count 6) 6))
		(= x1 (+ x i))
		(= x2 (+ x1 (+ i 1)))
		(= x3 (+ x2 (+ i 2)))
		(= x4 (+ x3 (+ i 3)))
		(= x5 (+ x4 (+ i 4)))
		(= x6 (+ x5 (+ i 5)))
	)
	(postLoop x6 (+ i 6) count)
))
(rule (=> 
	(and 
		(postLoop x i count)
		(not (< i (* count 6)))
	)
	exit
))
(query exit)
