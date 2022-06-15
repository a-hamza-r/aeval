(declare-rel inv1 ((Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) (Array Int Int) Int Int Int))
(declare-rel inv2 ((Array Int Int) (Array Int (Array Int Int)) (Array Int (Array Int Int)) (Array Int Int) Int Int Int))
(declare-var a (Array Int Int))
(declare-var b (Array Int (Array Int Int)))
(declare-var c (Array Int (Array Int Int)))
(declare-var d (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var c1 (Array Int (Array Int Int)))
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
    (inv1 a b c d 1 i count)
))

(rule (=> (and 
    (inv1 a b c d j i count) 
    (= a1 (store a j (- 1 (select a (- j 1)))))
    (< j (* count 8))) 
    (inv2 a1 b c d j 0 count)))

(rule (=> (and (inv2 a b c d j i count)
    (< i (* count 8))
    (= c1 (store c j (store (select c j) i (+ (select a j) (* (select (select b j) i) (select d j))))))
    (= i1 (+ i 1)))
    (inv2 a b c1 d j i1 count)))

(rule (=> (and (inv2 a b c d j i count)
 (not (< i (* count 8))) (= j1 (+ j 1))) (inv1 a b c d j1 i count)))

(rule (=> (and (inv1 a b c d j i count) (not (< j (* count 8)))) fail))

(query fail)