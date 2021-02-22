(declare-rel loop ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel exit ())
(declare-var i Int )
(declare-var i1 Int )
(declare-var i2 Int )
(declare-var i3 Int )
(declare-var i4 Int )
(declare-var j Int )
(declare-var j1 Int )
(declare-var j2 Int )
(declare-var j3 Int )
(declare-var j4 Int )
(declare-var j5 Int )
(declare-var j6 Int )
(declare-var j7 Int )
(declare-var j8 Int )
(declare-var t0 Int )
(declare-var t1 Int )
(declare-var t01 Int )
(declare-var t11 Int )
(declare-var t02 Int )
(declare-var t12 Int )
(declare-var t03 Int )
(declare-var t13 Int )
(declare-var index_limit Int )
(declare-var a_j Int )
(declare-var a_j1 Int )
(declare-var a_j2 Int )
(declare-var a_j3 Int )
(declare-var a_j4 Int )
(declare-var a_j5 Int )
(declare-var a_j6 Int )
(declare-var a_j7 Int )
(declare-var b_i Int )
(declare-var b_i1 Int )
(declare-var b_i2 Int )
(declare-var b_i3 Int )
(declare-var c_i Int )
(declare-var c_i1 Int )
(declare-var c_i2 Int )
(declare-var c_i3 Int )
(declare-var d_i Int )
(declare-var d_i1 Int )
(declare-var d_i2 Int )
(declare-var d_i3 Int )
(declare-var e_i Int )
(declare-var e_i1 Int )
(declare-var e_i2 Int )
(declare-var e_i3 Int )
(declare-var count Int )
(declare-var a_array (Array Int Int) )
(declare-var a_array1 (Array Int Int) )
(declare-var a_array2 (Array Int Int) )
(declare-var a_array3 (Array Int Int) )
(declare-var a_array4 (Array Int Int) )
(declare-var a_array5 (Array Int Int) )
(declare-var a_array6 (Array Int Int) )
(declare-var a_array7 (Array Int Int) )
(declare-var a_array8 (Array Int Int) )
(declare-var b_array (Array Int Int) )
(declare-var c_array (Array Int Int) )
(declare-var d_array (Array Int Int) )
(declare-var e_array (Array Int Int) )

(rule (=> 
	(and 
		(< 0 (- (* count 4) 1))
		
		(= b_i (select b_array 0))
		(= c_i (select c_array 0))
		(= d_i (select d_array 0))
		(= e_i (select e_array 0))
		(= t0 (* c_i d_i))
		(= t1 (* d_i e_i))
		(= a_j (+ b_i t0))
		(= a_j1 (+ b_i t1))
		(= a_array1 (store a_array (+ -1 1) a_j))
		(= a_array2 (store a_array1 (+ -1 2) a_j1))

		(= b_i1 (select b_array (+ 0 1)))
		(= c_i1 (select c_array (+ 0 1)))
		(= d_i1 (select d_array (+ 0 1)))
		(= e_i1 (select e_array (+ 0 1)))
		(= t01 (* c_i1 d_i1))
		(= t11 (* d_i1 e_i1))
		(= a_j2 (+ b_i1 t01))
		(= a_j3 (+ b_i1 t11))
		(= a_array3 (store a_array2 (+ -1 3) a_j2))
		(= a_array4 (store a_array3 (+ -1 4) a_j3))

		(= b_i2 (select b_array (+ 0 2)))
		(= c_i2 (select c_array (+ 0 2)))
		(= d_i2 (select d_array (+ 0 2)))
		(= e_i2 (select e_array (+ 0 2)))
		(= t02 (* c_i2 d_i2))
		(= t12 (* d_i2 e_i2))
		(= a_j4 (+ b_i2 t02))
		(= a_j5 (+ b_i2 t12))
		(= a_array5 (store a_array4 (+ -1 5) a_j4))
		(= a_array6 (store a_array5 (+ -1 6) a_j5))
		
		(= i 3)
		(= j 5)
	)
	(loop a_array6 b_array c_array d_array e_array i j count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array e_array i j count)

		(< i (- (* count 4) 1))
		
		(= b_i (select b_array i))
		(= c_i (select c_array i))
		(= d_i (select d_array i))
		(= e_i (select e_array i))
		(= t0 (* c_i d_i))
		(= t1 (* d_i e_i))
		(= a_j (+ b_i t0))
		(= a_j1 (+ b_i t1))
		(= a_array1 (store a_array (+ j 1) a_j))
		(= a_array2 (store a_array1 (+ j 2) a_j1))

		(= b_i1 (select b_array (+ i 1)))
		(= c_i1 (select c_array (+ i 1)))
		(= d_i1 (select d_array (+ i 1)))
		(= e_i1 (select e_array (+ i 1)))
		(= t01 (* c_i1 d_i1))
		(= t11 (* d_i1 e_i1))
		(= a_j2 (+ b_i1 t01))
		(= a_j3 (+ b_i1 t11))
		(= a_array3 (store a_array2 (+ j 3) a_j2))
		(= a_array4 (store a_array3 (+ j 4) a_j3))

		(= b_i2 (select b_array (+ i 2)))
		(= c_i2 (select c_array (+ i 2)))
		(= d_i2 (select d_array (+ i 2)))
		(= e_i2 (select e_array (+ i 2)))
		(= t02 (* c_i2 d_i2))
		(= t12 (* d_i2 e_i2))
		(= a_j4 (+ b_i2 t02))
		(= a_j5 (+ b_i2 t12))
		(= a_array5 (store a_array4 (+ j 5) a_j4))
		(= a_array6 (store a_array5 (+ j 6) a_j5))

		(= b_i3 (select b_array (+ i 3)))
		(= c_i3 (select c_array (+ i 3)))
		(= d_i3 (select d_array (+ i 3)))
		(= e_i3 (select e_array (+ i 3)))
		(= t03 (* c_i3 d_i3))
		(= t13 (* d_i3 e_i3))
		(= a_j6 (+ b_i3 t03))
		(= a_j7 (+ b_i3 t13))
		(= a_array7 (store a_array6 (+ j 7) a_j6))
		(= a_array8 (store a_array7 (+ j 8) a_j7))
	)
	(loop a_array8 b_array c_array d_array e_array (+ i 4) (+ j 8) count)
))
(rule (=> 
	(and 
		(loop a_array b_array c_array d_array e_array i j count)
		(not (< i (- (* count 4) 1)))
	)
	exit
))
(query exit)