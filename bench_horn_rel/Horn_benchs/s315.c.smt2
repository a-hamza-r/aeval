(declare-rel loop ((Array Int Int) Int Int Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var i1 Int )
(declare-var x Int )
(declare-var x1 Int )
(declare-var index Int )
(declare-var index1 Int )
(declare-var index_limit Int )
(declare-var a_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )

(rule (=> 
	(and 
		(= x (select a_array 0))
		(= index 0)
		(= i 0)
	)
	(loop a_array i count x index)
))
(rule (=> 
	(and 
		(loop a_array i count x index)
		(< i (* count 8))
		(= a_i (select a_array i))
		(= x1 (ite (> a_i x) a_i x))
		(= index1 (ite (> a_i x) i index))
	)
	(loop a_array (+ i 1) count x1 index1)
))
(rule (=> 
	(and 
		(loop a_array i count x index)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)