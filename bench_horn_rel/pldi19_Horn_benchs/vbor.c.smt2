(declare-rel loop ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var i1 Int )
(declare-var a_i Int )
(declare-var ip_i Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var x_array (Array Int Int) )
(declare-var x_array1 (Array Int Int) )
(declare-var b_array (Array Int Int) )
(declare-var c_array (Array Int Int) )
(declare-var d_array (Array Int Int) )
(declare-var e_array (Array Int Int) )
(declare-var aa_array (Array Int Int) )

(rule (=> 
	(and 
		(= i 0)
		(> count 0)
	)
	(loop a_array b_array c_array d_array e_array aa_array x_array i count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array e_array aa_array x_array i count)
		(< i (* count 8))
		(= a_i (select a_array i))
		(= b_i (select b_array i))
		(= c_i (select c_array i))
		(= d_i (select d_array i))
		(= e_i (select e_array i))
	)
	(loop a_array b_array c_array d_array e_array aa_array x_array1 (+ i 1) count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array e_array aa_array x_array i count)
		(not (< i (* count 8)))
	)
	exit
))
(query exit)