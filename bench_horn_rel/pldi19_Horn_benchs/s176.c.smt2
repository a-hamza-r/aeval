(declare-rel inv1 ((Array Int Int) (Array Int Int) (Array Int Int) Int Int Int))
(declare-rel inv2 ((Array Int Int) (Array Int Int) (Array Int Int) Int Int Int))
(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var c (Array Int Int))
(declare-var a1 (Array Int Int))
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
    (inv1 a b c 0 i count)
))

(rule (=> (and (inv1 a b c j i count) (< j count)) (inv2 a b c j 0 count)))

(rule (=> (and (inv2 a b c j i count)
 (< i (* count 4))
 (= a1 (store a i (+ (select a i) (* (select b (- (+ i (* count 4)) (+ j 1))) (select c j)))))
 (= i1 (+ i 1)))
  (inv2 a1 b c j i1 count)))

(rule (=> (and (inv2 a b c j i count)
 (not (< i (* count 4))) (= j1 (+ j 1))) (inv1 a b c j1 i count)))

(rule (=> (and (inv1 a b c j i count) (not (< j count))) fail))

(query fail)