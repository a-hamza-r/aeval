(declare-fun inv_0 (Int Int) Bool)
(declare-fun inv_1 (Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int)) (=> (and (= 1 |_FH_0'|) (= (- 1) |_FH_1'|)) (inv_0 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= |_FH_0'| (+ (- _FH_0) (- _FH_0))) (= |_FH_1'| _FH_1) (>= _FH_0 0) (inv_0 _FH_0 _FH_1)) (inv_0 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (inv_0 _FH_0 _FH_1) (not (>= _FH_0 0))) (inv_1 _FH_0 _FH_1))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (< _FH_0 0) (= |_FH_0'| (+ (- _FH_0) (- _FH_0))) (= |_FH_1'| (* 4 _FH_1)) (inv_1 _FH_0 _FH_1)) (inv_1 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (> _FH_0 5143523) (distinct 0 (+ _FH_0 _FH_1)) (inv_1 _FH_0 _FH_1)) false)))

(check-sat)
