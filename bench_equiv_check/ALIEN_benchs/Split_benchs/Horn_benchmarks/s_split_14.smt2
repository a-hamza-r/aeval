(declare-rel inv (Int Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var z0 Int)
(declare-var z1 Int)
(declare-var i0 Int)
(declare-var i1 Int)
(declare-var N Int)

(declare-rel fail ())

(rule (=> (and (= x0 -100) (= z0 -100) (= i0 0) (= N 105))
    (inv x0 z0 i0 N)))

(rule (=> (and
        (inv x0 z0 i0 N)
        (< i0 N)
        (= i1 (+ i0 1))
        (= x1 (mod (+ x0 1) 5))
        (= z1 (ite (< z0 4) (+ z0 1) (mod z0 4))))
    (inv x1 z1 i1 N)))

(rule (=> (and (inv x0 z0 i0 N) (>= i0 N)
    (not (= x0 z0))) fail))

(query fail)
