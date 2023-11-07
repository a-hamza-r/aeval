(declare-rel loop ((Array Int (Array Int Int)) (Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var i1 Int )
(declare-var count Int )
(declare-var a (Array Int (Array Int Int)) )
(declare-var b (Array Int Int) )
(declare-var c (Array Int Int) )
(declare-var a1 (Array Int (Array Int Int)) )

(rule (=> 
	(and 
		(= i 1)
		(> count 0)
	)
	(loop a b c i count)
))
(rule (=> 
	(and 
		(loop a b c i count)
		(< i (* count 8))
		(= a1 (store a 0 (store (select a 0) i (+ (select (select a 1) (- i 1)) (* (select b i) (select c 1))))))
		(= i1 (+ i 1))
	)
	(loop a1 b c i1 count)
))
(rule (=> 
	(and 
		(loop a b c i count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)