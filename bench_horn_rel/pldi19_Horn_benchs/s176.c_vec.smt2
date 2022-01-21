(declare-rel inv1 ((Array Int Int) (Array Int Int) (Array Int Int) Int Int Int))
(declare-rel inv2 ((Array Int Int) (Array Int Int) (Array Int Int) Int Int Int))
(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var c (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var a2 (Array Int Int))
(declare-var a3 (Array Int Int))
(declare-var a4 (Array Int Int))
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

(rule (=> (and (inv1 a b c j i count) (< j (* count 4))) (inv2 a b c j 0 count)))

(rule (=> (and (inv2 a b c j i count)
 (< i (* count 4))
 (= a1 (store a i (+ (select a i) (* (select b (- (+ i (* count 4)) (+ j 1))) (select c j)))))
 (= a2 (store a1 (+ i 1) (+ (select a1 (+ i 1)) (* (select b (- (+ (+ i 1) (* count 4)) (+ j 1))) (select c j)))))
 (= a3 (store a2 (+ i 2) (+ (select a2 (+ i 2)) (* (select b (- (+ (+ i 2) (* count 4)) (+ j 1))) (select c j)))))
 (= a4 (store a3 (+ i 3) (+ (select a3 (+ i 3)) (* (select b (- (+ (+ i 3) (* count 4)) (+ j 1))) (select c j)))))
 (= i1 (+ i 4)))
  (inv2 a4 b c j i1 count)))

(rule (=> (and (inv2 a b c j i count)
 (not (< i (* count 4))) (= j1 (+ j 1))) (inv1 a b c j1 i count)))

(rule (=> (and (inv1 a b c j i count) (not (< j (* count 4)))) fail))

(query fail)