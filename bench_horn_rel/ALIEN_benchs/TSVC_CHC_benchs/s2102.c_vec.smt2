(declare-rel inv1 ((Array Int (Array Int Int)) Int Int Int))
(declare-rel inv2 ((Array Int (Array Int Int)) Int Int Int))
(declare-var aa (Array Int (Array Int Int)))
(declare-var aa1 (Array Int (Array Int Int)))
(declare-var aa2 (Array Int (Array Int Int)))
(declare-var aa3 (Array Int (Array Int Int)))
(declare-var aa4 (Array Int (Array Int Int)))
(declare-var aa5 (Array Int (Array Int Int)))
(declare-var aa6 (Array Int (Array Int Int)))
(declare-var aa7 (Array Int (Array Int Int)))
(declare-var aa8 (Array Int (Array Int Int)))
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
    (inv1 aa 0 i count)
))

(rule (=> (and (inv1 aa j i count) (< j (* count 8))) (inv2 aa j 0 count)))

(rule (=> (and (inv2 aa j i count)
 (< i (* count 8))
 (= aa1 (store aa j (store (select aa j) i 0)))
 (= aa2 (store aa1 j (store (select aa1 j) (+ i 1) 0)))
 (= aa3 (store aa2 j (store (select aa2 j) (+ i 2) 0)))
 (= aa4 (store aa3 j (store (select aa3 j) (+ i 3) 0)))
 (= aa5 (store aa4 j (store (select aa4 j) (+ i 4) 0)))
 (= aa6 (store aa5 j (store (select aa5 j) (+ i 5) 0)))
 (= aa7 (store aa6 j (store (select aa6 j) (+ i 6) 0)))
 (= aa8 (store aa7 j (store (select aa7 j) (+ i 7) 0)))
 (= i1 (+ i 8)))
  (inv2 aa8 j i1 count)))

(rule (=> (and 
    (inv2 aa j i count)
    (not (< i (* count 8))) 
    (= aa1 (store aa j (store (select aa j) j 1)))
    (= j1 (+ j 1))) 
    (inv1 aa1 j1 i count)))

(rule (=> (and (inv1 aa j i count) (not (< j (* count 8)))) fail))

(query fail)