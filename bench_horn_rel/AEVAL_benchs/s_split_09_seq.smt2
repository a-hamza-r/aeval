(declare-fun inv_0 (Int) Bool)
(declare-fun inv_1 (Int) Bool)

(assert (forall ((|_FH_0'| Int)) (=> (and (= 0 |_FH_0'|)) (inv_0 |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 2)) (distinct _FH_0 9998) (inv_0 _FH_0)) (inv_0 |_FH_0'|))))

(assert (forall ((_FH_0 Int)) (=> (and (inv_0 _FH_0) (not (distinct _FH_0 9998))) (inv_1 _FH_0))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int)) (=> (and (= _FH_0 9998) (= |_FH_0'| 1) (inv_1 _FH_0)) (inv_1 |_FH_0'|))))

(assert (forall ((_FH_0 Int)) (=> (and (= 0 (mod _FH_0 4)) (> _FH_0 9996) (inv_1 _FH_0)) false)))

(check-sat)
