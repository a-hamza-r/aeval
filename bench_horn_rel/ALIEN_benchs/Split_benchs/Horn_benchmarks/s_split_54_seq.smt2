(declare-fun inv_0 (Int Int Int) Bool)
(declare-fun inv_1 (Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int)) (=> (and (= 0 |_FH_0'|) (= 8000 |_FH_1'|) (= 0 |_FH_2'|)) (inv_0 |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int)) (=> (and (distinct 16000 _FH_0) (< _FH_0 8000) (= |_FH_0'| (+ _FH_0 1)) (= |_FH_2'| (+ _FH_2 1)) (= |_FH_1'| (+ _FH_1 (- 1))) (inv_0 _FH_0 _FH_1 _FH_2)) (inv_0 |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int)) (=> (and (inv_0 _FH_0 _FH_1 _FH_2) (not (< _FH_0 8000))) (inv_1 _FH_0 _FH_1 _FH_2))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int)) (=> (and (distinct 16000 _FH_0) (>= _FH_0 8000) (= |_FH_0'| (+ _FH_0 1)) (= |_FH_2'| (+ _FH_2 (- 1))) (= |_FH_1'| (+ _FH_1 1)) (inv_1 _FH_0 _FH_1 _FH_2)) (inv_1 |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int)) (=> (and (= 16000 _FH_0) (or (< _FH_1 8000) (> _FH_1 8000) (< _FH_2 0) (> _FH_2 0)) (inv_1 _FH_0 _FH_1 _FH_2)) false)))

(check-sat)
