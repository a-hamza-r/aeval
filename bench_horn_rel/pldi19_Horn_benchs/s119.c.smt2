(declare-var a (Array Int (Array Int Int)))
(declare-var a1 (Array Int (Array Int Int)))
(declare-var b (Array Int (Array Int Int)))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var count Int)

(declare-rel inv1 ((Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int Int))
(declare-rel inv2 ((Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int Int))
(declare-rel fail ())

(rule (=> 
    (and 
        (> count 0)
    )
    (inv1 a b 1 j count)
))

(rule (=> (and (inv1 a b i j count) (< i count) (= j 1)) (inv2 a b i j count)))

(rule (=> (and (inv2 a b i j count)
  (< j (* count 8))
  (= a1 (store a i (store (select a i) j (+ (select (select a (- i 1)) (- j 1)) (select (select b i) j)))))
  (= j1 (+ j 1)))
    (inv2 a1 b i j1 count)))

(rule (=> (and (inv2 a b i j count)
  (not (< j (* count 8))) (= i1 (+ i 1))) (inv1 a b i1 j count)))

(rule (=> (and (inv1 a b i j count) (not (< i count))) fail))

(query fail)
