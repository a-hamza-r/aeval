(declare-rel loop ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var c_i Int )
(declare-var d_i Int )
(declare-var index_limit Int )
(declare-var a_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array1 (Array Int Int) )
(declare-var b_array (Array Int Int) )
(declare-var c_array (Array Int Int) )
(declare-var c_array1 (Array Int Int) )
(declare-var d_array (Array Int Int) )
(declare-var e_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
		(> count 0)
	)
	(loop a_array b_array c_array d_array e_array i count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array e_array i count)
		(< i (- (* count 8) 1))
		(= d_i (select d_array i))
		(= c_i (ite (< (select b_array i) 0) (+ (select a_array i) (* d_i d_i)) (select c_array (+ i 1))))
		(= a_i (ite (< (select b_array i) 0) (select a_array i) (+ (select c_array i) (* d_i (select e_array i)))))
		(= c_array1 (store c_array (+ i 1) c_i))
		(= a_array1 (store a_array i a_i))
	)
	(loop a_array1 b_array c_array1 d_array e_array (+ i 1) count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array e_array i count)
		(not (< i (- (* count 8) 1)))
	)
	exit
))
(query exit)