(declare-rel inv1 ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int Int))
(declare-rel inv2 ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int Int))
(declare-var aa (Array Int (Array Int Int)))
(declare-var bb (Array Int (Array Int Int)))
(declare-var cc (Array Int (Array Int Int)))
(declare-var aa1 (Array Int (Array Int Int)))
(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var b (Array Int Int))
(declare-var c (Array Int Int))
(declare-var d (Array Int Int))
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
    (inv1 a b c d aa bb cc 0 i count)
))

(rule (=> (and (inv1 a b c d aa bb cc j i count) (< j (* count 8))) (inv2 a b c d aa bb cc j 0 count)))

(rule (=> (and (inv2 a b c d aa bb cc j i count)
 (< i (* count 8))
 (= aa1 (store aa j (store (select aa j) i (+ (select (select aa j) i) (* (select (select bb j) i) (select (select cc j) i))))))
 (= i1 (+ i 1)))
  (inv2 a b c d aa1 bb cc j i1 count)))

(rule (=> (and 
    (inv2 a b c d aa bb cc j i count)
    (not (< i (* count 8))) 
    (= a1 (store a j (+ (select b j) (* (select c j) (select d j)))))
    (= j1 (+ j 1))) 
    (inv1 a1 b c d aa bb cc j1 i count)))

(rule (=> (and (inv1 a b c d aa bb cc j i count) (not (< j (* count 8)))) fail))

(query fail)