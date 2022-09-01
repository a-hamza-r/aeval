(declare-fun inv_0 (Int Int Int Int) Bool)
(declare-fun inv_1 (Int Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int) (|_FH_3'| Int)) (=> (and (= 52 |_FH_0'|) (= 97 |_FH_1'|) (= 0 |_FH_3'|) (= (- 76) |_FH_2'|)) (inv_0 |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int)) (=> (and (= |_FH_0'| (+ (* (- 7) _FH_0) 13)) (= |_FH_1'| (+ (* (- 2) _FH_1) 54)) (= |_FH_2'| (+ (* 3 _FH_1) (* 4 _FH_2) (* (- 5) _FH_0) (- 8754))) (= |_FH_3'| (+ _FH_3 0)) (<= |_FH_2'| 0) (<= (+ (* 4 _FH_2) (* 3 _FH_1) (* (- 5) _FH_0)) 8754) (inv_0 _FH_0 _FH_1 _FH_2 _FH_3)) (inv_0 |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int)) (=> (and (inv_0 _FH_0 _FH_1 _FH_2 _FH_3) (not (<= (+ (* 4 _FH_2) (* 3 _FH_1) (* (- 5) _FH_0)) 8754))) (inv_1 _FH_0 _FH_1 _FH_2 _FH_3))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int)) (=> (and (= |_FH_0'| (+ (* (- 7) _FH_0) 13)) (= |_FH_1'| (+ (* (- 2) _FH_1) 54)) (= |_FH_2'| (+ (* 3 _FH_1) (* 4 _FH_2) (* (- 5) _FH_0) (- 8754))) (> |_FH_2'| 0) (= |_FH_3'| (+ _FH_3 (- _FH_0))) (> (+ (* 4 _FH_2) (* 3 _FH_1) (* (- 5) _FH_0)) 8754) (inv_1 _FH_0 _FH_1 _FH_2 _FH_3)) (inv_1 |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int)) (=> (and (<= _FH_3 0) (>= _FH_1 80914) (inv_1 _FH_0 _FH_1 _FH_2 _FH_3)) false)))

(check-sat)
