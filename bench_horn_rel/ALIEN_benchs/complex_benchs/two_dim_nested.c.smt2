(declare-rel inv1 ((Array Int (Array Int Int)) Int Int Int Int))
(declare-rel inv2 ((Array Int (Array Int Int)) Int Int Int Int))
(declare-var a (Array Int (Array Int Int)))
(declare-var a1 (Array Int (Array Int Int)))
(declare-var M Int)
(declare-var N Int)
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)

(declare-rel fail ())

(rule (=> 
    (and 
        (> M 0)
        (> N 0)
    )
    (inv1 a 0 j M N)
))

(rule (=> (and (inv1 a i j M N) (< i M)) (inv2 a i 0 M N)))

(rule (=> (and (inv2 a i j M N)
 (< j (* N 8))
 (= a1 (store a i (store (select a i) j 0)))
 (= j1 (+ j 1)))
  (inv2 a1 i j1 M N)))

(rule (=> (and (inv2 a i j M N)
 (not (< j (* N 8))) (= i1 (+ i 1))) (inv1 a i1 j M N)))

(rule (=> (and (inv1 a i j M N) (not (< i (* M 8)))
 (<= 0 i1) (< i1 M 8)
  (<= 0 j1) (< j1 (* N 8))
   (not (= (select (select a i1) j1) 0))) fail))

(query fail)