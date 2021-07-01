(declare-rel loop ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var mult Int )
(declare-var index_limit Int )
(declare-var a_i Int )
(declare-var c_i Int )
(declare-var c_select Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
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
		(< i (* count 8))
		(= a_i (select a_array i))
		(= c_select (select c_array i))
		(= mult (select d_array i) (select e_array i))
		(= c_i (ite (and (< a_i 0) (> (select b_array i) a_i)) (+ c_select mult) c_select))
		(= c_array1 (store c_array i c_i))
	)
	(loop a_array b_array c_array1 d_array e_array (+ i 1) count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array e_array i count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)