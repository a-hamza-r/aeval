(declare-fun inv_0 (Int) Bool)
(declare-fun inv_1 (Int) Bool)

(assert (forall ((|_FH_0'| Int)) (=> (and (= 0 |_FH_0'|)) (inv_0 |_FH_0'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int)) (=> (and (< (div _FH_0 5) 200) (= |_FH_0'| (+ _FH_0 1)) (inv_0 _FH_0)) (inv_0 |_FH_0'|))))

(assert (forall ((_FH_0 Int)) (=> (and (inv_0 _FH_0) (not (< (div _FH_0 5) 200))) (inv_1 _FH_0))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 5)) (>= (div _FH_0 5) 200) (inv_1 _FH_0)) (inv_1 |_FH_0'|))))

(assert (forall ((_FH_0 Int)) (=> (and (>= _FH_0 2000) (distinct (mod _FH_0 5) 0) (inv_1 _FH_0)) false)))

(check-sat)
