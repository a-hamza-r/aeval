(declare-rel inv1 ((Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int Int))
(declare-rel inv2 ((Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int Int))
(declare-var a (Array Int (Array Int Int)))
(declare-var array (Array Int Int))
(declare-var b (Array Int (Array Int Int)))
(declare-var c (Array Int (Array Int Int)))
(declare-var array1 (Array Int Int))
(declare-var count Int)
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)

(declare-rel fail ())

(rule (=> 
    (and 
        (> count 0)
    )
    (inv1 array a b c 0 j count)
))

(rule (=> (and (inv1 array a b c i j count) (< i (* count 8))) (inv2 array a b c i 0 count)))

(rule (=> (and (inv2 array a b c i j count)
 (< j (* count 8))
 (= array1 (store array (+ (* i count) j) (+ (select (select a i) j) (* (select (select b i) j) (select (select c i) j)))))
 (= j1 (+ j 1)))
  (inv2 array1 a b c i j1 count)))

(rule (=> (and (inv2 array a b c i j count)
 (not (< i (* count 8))) (= i1 (+ i 1))) (inv1 array a b c i1 j count)))

(rule (=> (and (inv1 array a b c i j count) (not (< i (* count 8)))) fail))

(query fail)