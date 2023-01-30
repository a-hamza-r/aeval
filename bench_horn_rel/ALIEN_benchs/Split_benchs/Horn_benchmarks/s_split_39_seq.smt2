(declare-fun inv_0 (Int Int) Bool)
(declare-fun inv_1 (Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int)) (=> (and (= 0 |_FH_0'|) (= 0 |_FH_1'|)) (inv_0 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (= |_FH_0'| (div _FH_0 10)) (>= (* 5 _FH_0) _FH_1) (= |_FH_1'| (+ _FH_1 1)) (>= (+ (* 5 _FH_0) (* (- 1) _FH_1)) 0) (inv_0 _FH_0 _FH_1)) (inv_0 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (inv_0 _FH_0 _FH_1) (not (>= (+ (* 5 _FH_0) (* (- 1) _FH_1)) 0))) (inv_1 _FH_0 _FH_1))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int)) (=> (and (< (* 5 _FH_0) _FH_1) (= |_FH_0'| (+ _FH_0 1)) (= |_FH_1'| (+ _FH_1 0)) (< (+ (* 5 _FH_0) (* (- 1) _FH_1)) 0) (inv_1 _FH_0 _FH_1)) (inv_1 |_FH_0'| |_FH_1'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int)) (=> (and (> _FH_1 50) (<= _FH_1 _FH_0) (inv_1 _FH_0 _FH_1)) false)))

(check-sat)
