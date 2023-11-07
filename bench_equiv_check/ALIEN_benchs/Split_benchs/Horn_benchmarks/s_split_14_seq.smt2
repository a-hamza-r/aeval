(declare-fun inv_0 (Int Int Int Int) Bool)
(declare-fun inv_1 (Int Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int) (|_FH_3'| Int)) (=> (and (= (- 100) |_FH_0'|) (= (- 100) |_FH_1'|) (= 0 |_FH_2'|) (= 105 |_FH_3'|)) (inv_0 |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int)) (=> (and (= |_FH_0'| (mod (+ _FH_0 1) 5)) (< _FH_1 4) (= |_FH_1'| (+ _FH_1 1)) (= |_FH_2'| (+ _FH_2 1)) (= |_FH_3'| _FH_3) (inv_0 _FH_0 _FH_1 _FH_2 _FH_3)) (inv_0 |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int)) (=> (and (inv_0 _FH_0 _FH_1 _FH_2 _FH_3) (not (< _FH_1 4))) (inv_1 _FH_0 _FH_1 _FH_2 _FH_3))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int)) (=> (and (< _FH_2 _FH_3) (= |_FH_0'| (mod (+ _FH_0 1) 5)) (= |_FH_1'| (mod _FH_1 4)) (>= _FH_1 4) (= |_FH_2'| (+ _FH_2 1)) (= |_FH_3'| _FH_3) (inv_1 _FH_0 _FH_1 _FH_2 _FH_3)) (inv_1 |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int)) (=> (and (>= _FH_2 _FH_3) (inv_1 _FH_0 _FH_1 _FH_2 _FH_3)) false)))

(check-sat)
