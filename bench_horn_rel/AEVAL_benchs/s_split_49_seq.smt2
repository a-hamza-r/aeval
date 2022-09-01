(declare-fun inv_0 (Int Int) Bool)
(declare-fun inv_1 (Int Int) Bool)
(declare-fun inv_2 (Int Int) Bool)
(declare-fun inv_3 (Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int)) (=> (and (= 0 |_FH_0'|) (= 0 |_FH_1'|)) (inv_0 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (= |_FH_1'| (+ _FH_1 (- 2))) (< _FH_0 2500) (< _FH_0 7500) (inv_0 _FH_0 _FH_1)) (inv_0 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (inv_0 _FH_0 _FH_1) (not (< _FH_0 2500))) (inv_1 _FH_0 _FH_1))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (>= _FH_0 2500) (= |_FH_1'| (+ _FH_1 1)) (< _FH_0 7500) (inv_1 _FH_0 _FH_1)) (inv_1 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (inv_1 _FH_0 _FH_1) (not (and (>= _FH_0 2500) (< _FH_0 7500)))) (inv_2 _FH_0 _FH_1))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (>= _FH_0 7500) (= |_FH_1'| (+ _FH_1 1)) (< _FH_0 12500) (inv_2 _FH_0 _FH_1)) (inv_2 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (inv_2 _FH_0 _FH_1) (not (and (>= _FH_0 7500) (< _FH_0 12500)))) (inv_3 _FH_0 _FH_1))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (>= _FH_0 7500) (>= _FH_0 12500) (= |_FH_1'| (+ _FH_1 (- 2))) (inv_3 _FH_0 _FH_1)) (inv_3 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (= 15000 _FH_0) (distinct _FH_1 0) (inv_3 _FH_0 _FH_1)) false)))

(check-sat)
