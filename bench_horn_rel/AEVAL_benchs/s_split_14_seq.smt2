(declare-fun inv_0 (Int Int) Bool)
(declare-fun inv_1 (Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int)) (=> (and (= (- 100) |_FH_0'|) (= (- 100) |_FH_1'|)) (inv_0 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= |_FH_0'| (mod (+ _FH_0 1) 5)) (< _FH_1 4) (= |_FH_1'| (+ _FH_1 1)) (inv_0 _FH_0 _FH_1)) (inv_0 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (inv_0 _FH_0 _FH_1) (not (< _FH_1 4))) (inv_1 _FH_0 _FH_1))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= |_FH_0'| (mod (+ _FH_0 1) 5)) (= |_FH_1'| (mod _FH_1 4)) (>= _FH_1 4) (inv_1 _FH_0 _FH_1)) (inv_1 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (>= _FH_1 0) (distinct _FH_0 _FH_1) (inv_1 _FH_0 _FH_1)) false)))

(check-sat)
