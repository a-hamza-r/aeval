(declare-rel inv1 ((Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int Int))
(declare-rel inv2 ((Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int Int))
(declare-var a (Array Int (Array Int Int)))
(declare-var array (Array Int Int))
(declare-var b (Array Int (Array Int Int)))
(declare-var b1 (Array Int (Array Int Int)))
(declare-var c (Array Int (Array Int Int)))
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
    (inv1 array a b c 1 i count)
))

(rule (=> (and (inv1 array a b c j i count) (< j count)) (inv2 array a b c j 0 count)))

(rule (=> (and (inv2 array a b c j i count)
 (< i (* count 8))
 (= b1 (store b j (store (select b j) i (+ (select (select b (- j 1)) i) (* (select array (- (+ i j))) (select (select c j) i))))))
 (= i1 (+ i 1)))
  (inv2 array a b1 c j i1 count)))

(rule (=> (and (inv2 array a b c j i count)
 (not (< j (* count 8))) (= j1 (+ j 1))) (inv1 array a b c j1 i count)))

(rule (=> (and (inv1 array a b c j i count) (not (< j count))) fail))

(query fail)