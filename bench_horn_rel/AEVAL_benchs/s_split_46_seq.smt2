(declare-fun inv_0 (Int Int) Bool)
(declare-fun inv_1 (Int Int) Bool)
(declare-fun inv_2 (Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int)) (=> (and (= 0 |_FH_0'|)) (inv_0 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (< (div _FH_0 5) 200) (= |_FH_1'| _FH_1) (distinct _FH_0 1000) (= |_FH_0'| (+ _FH_0 1)) (inv_0 _FH_0 _FH_1)) (inv_0 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (inv_0 _FH_0 _FH_1) (not (< (div _FH_0 5) 200))) (inv_1 _FH_0 _FH_1))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= _FH_0 1000) (= |_FH_1'| 0) (= |_FH_0'| (+ _FH_0 5)) (>= (div _FH_0 5) 200) (inv_1 _FH_0 _FH_1)) (inv_1 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (inv_1 _FH_0 _FH_1) (not (= _FH_0 1000))) (inv_2 _FH_0 _FH_1))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= |_FH_1'| _FH_1) (distinct _FH_0 1000) (= |_FH_0'| (+ _FH_0 5)) (>= (div _FH_0 5) 200) (inv_2 _FH_0 _FH_1)) (inv_2 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (distinct _FH_1 0) (>= _FH_0 2000) (inv_2 _FH_0 _FH_1)) false)))

(check-sat)
