(declare-fun inv_0 (Int Int) Bool)
(declare-fun inv_1 (Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int)) (=> (and (= 0 |_FH_0'|) (= 7500 |_FH_1'|)) (inv_0 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= 0 (mod _FH_0 2)) (= |_FH_0'| (+ _FH_0 2)) (= |_FH_1'| (+ _FH_1 0)) (< _FH_0 5000) (= (mod _FH_0 2) 0) (inv_0 _FH_0 _FH_1)) (inv_0 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (inv_0 _FH_0 _FH_1) (not (and (< _FH_0 5000) (= (mod _FH_0 2) 0)))) (inv_1 _FH_0 _FH_1))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= 0 (mod _FH_0 2)) (>= _FH_0 5000) (= |_FH_0'| (+ _FH_0 2)) (= |_FH_1'| (+ _FH_1 1)) (= (mod _FH_0 2) 0) (inv_1 _FH_0 _FH_1)) (inv_1 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (= 10000 _FH_0) (distinct _FH_1 10000) (inv_1 _FH_0 _FH_1)) false)))

(check-sat)
