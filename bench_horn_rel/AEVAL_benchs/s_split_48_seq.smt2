(declare-fun inv_0 (Int Int) Bool)
(declare-fun inv_1 (Int Int) Bool)
(declare-fun inv_2 (Int Int) Bool)
(declare-fun inv_3 (Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int)) (=> (and (= 0 |_FH_0'|) (= 0 |_FH_1'|)) (inv_0 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (< _FH_0 5000) (= |_FH_1'| (+ _FH_1 1)) (< _FH_0 4000) (inv_0 _FH_0 _FH_1)) (inv_0 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (inv_0 _FH_0 _FH_1) (not (< _FH_0 4000))) (inv_1 _FH_0 _FH_1))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (< _FH_0 5000) (>= _FH_0 4000) (= |_FH_1'| (+ _FH_1 4)) (inv_1 _FH_0 _FH_1)) (inv_1 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (inv_1 _FH_0 _FH_1) (not (and (< _FH_0 5000) (>= _FH_0 4000)))) (inv_2 _FH_0 _FH_1))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (= |_FH_1'| (+ _FH_1 (- 4))) (< _FH_0 6000) (>= _FH_0 5000) (inv_2 _FH_0 _FH_1)) (inv_2 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (inv_2 _FH_0 _FH_1) (not (and (< _FH_0 6000) (>= _FH_0 5000)))) (inv_3 _FH_0 _FH_1))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (>= _FH_0 6000) (= |_FH_1'| (+ _FH_1 (- 1))) (>= _FH_0 5000) (inv_3 _FH_0 _FH_1)) (inv_3 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (= 10000 _FH_0) (distinct _FH_1 0) (inv_3 _FH_0 _FH_1)) false)))

(check-sat)
