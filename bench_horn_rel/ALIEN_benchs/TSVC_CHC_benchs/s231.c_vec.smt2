(declare-rel inv1 ((Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int Int))
(declare-rel inv2 ((Array Int (Array Int Int)) (Array Int (Array Int Int)) Int Int Int))
(declare-var a (Array Int (Array Int Int)))
(declare-var b (Array Int (Array Int Int)))
(declare-var a1 (Array Int (Array Int Int)))
(declare-var a2 (Array Int (Array Int Int)))
(declare-var a3 (Array Int (Array Int Int)))
(declare-var a4 (Array Int (Array Int Int)))
(declare-var a5 (Array Int (Array Int Int)))
(declare-var a6 (Array Int (Array Int Int)))
(declare-var a7 (Array Int (Array Int Int)))
(declare-var a8 (Array Int (Array Int Int)))
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
    (inv1 a b 1 i count)
))

(rule (=> (and (inv1 a b j i count) (< j count)) (inv2 a b j 0 count)))

(rule (=> (and (inv2 a b j i count)
 (< i (* count 8))
 (= a1 (store a j (store (select a j) i (+ (select (select a (- j 1)) i) (select (select b j) i)))))
 (= a2 (store a1 j (store (select a1 j) (+ i 1) (+ (select (select a1 (- j 1)) (+ i 1)) (select (select b j) (+ i 1))))))
 (= a3 (store a2 j (store (select a2 j) (+ i 2) (+ (select (select a2 (- j 1)) (+ i 2)) (select (select b j) (+ i 2))))))
 (= a4 (store a3 j (store (select a3 j) (+ i 3) (+ (select (select a3 (- j 1)) (+ i 3)) (select (select b j) (+ i 3))))))
 (= a5 (store a4 j (store (select a4 j) (+ i 4) (+ (select (select a4 (- j 1)) (+ i 4)) (select (select b j) (+ i 4))))))
 (= a6 (store a5 j (store (select a5 j) (+ i 5) (+ (select (select a5 (- j 1)) (+ i 5)) (select (select b j) (+ i 5))))))
 (= a7 (store a6 j (store (select a6 j) (+ i 6) (+ (select (select a6 (- j 1)) (+ i 6)) (select (select b j) (+ i 6))))))
 (= a8 (store a7 j (store (select a7 j) (+ i 7) (+ (select (select a7 (- j 1)) (+ i 7)) (select (select b j) (+ i 7))))))
 (= i1 (+ i 8)))
  (inv2 a8 b j i1 count)))

(rule (=> (and (inv2 a b j i count)
 (not (< i (* count 8))) (= j1 (+ j 1))) (inv1 a b j1 i count)))

(rule (=> (and (inv1 a b j i count) (not (< j count))) fail))

(query fail)