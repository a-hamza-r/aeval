(declare-fun inv_0 (Int Int Int Int) Bool)
(declare-fun inv_1 (Int Int Int Int) Bool)
(declare-fun inv_2 (Int Int Int Int) Bool)
(declare-fun inv_3 (Int Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int) (|_FH_3'| Int)) (=> (and (= 0 |_FH_0'|) (= 1000 |_FH_1'|) (= 2000 |_FH_2'|) (= 3000 |_FH_3'|)) (inv_0 |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (= |_FH_3'| (+ _FH_3 0)) (< _FH_2 3000) (= |_FH_2'| (+ _FH_2 0)) (< _FH_1 2000) (= |_FH_1'| (+ _FH_1 0)) (< _FH_0 1000) (inv_0 _FH_0 _FH_1 _FH_2 _FH_3)) (inv_0 |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int)) (=> (and (inv_0 _FH_0 _FH_1 _FH_2 _FH_3) (not (and (< _FH_2 3000) (< _FH_1 2000) (< _FH_0 1000)))) (inv_1 _FH_0 _FH_1 _FH_2 _FH_3))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int)) (=> (and (= |_FH_0'| (+ _FH_0 1)) (>= _FH_0 1000) (= |_FH_3'| (+ _FH_3 0)) (< _FH_2 3000) (= |_FH_2'| (+ _FH_2 0)) (< _FH_1 2000) (= |_FH_1'| (+ _FH_1 1)) (inv_1 _FH_0 _FH_1 _FH_2 _FH_3)) (inv_1 |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int)) (=> (and (inv_1 _FH_0 _FH_1 _FH_2 _FH_3) (not (and (>= _FH_0 1000) (< _FH_2 3000) (< _FH_1 2000)))) (inv_2 _FH_0 _FH_1 _FH_2 _FH_3))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int)) (=> (and (>= _FH_1 2000) (= |_FH_0'| (+ _FH_0 1)) (>= _FH_0 1000) (= |_FH_3'| (+ _FH_3 0)) (< _FH_2 3000) (= |_FH_2'| (+ _FH_2 1)) (= |_FH_1'| (+ _FH_1 1)) (inv_2 _FH_0 _FH_1 _FH_2 _FH_3)) (inv_2 |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int)) (=> (and (inv_2 _FH_0 _FH_1 _FH_2 _FH_3) (not (and (>= _FH_1 2000) (>= _FH_0 1000) (< _FH_2 3000)))) (inv_3 _FH_0 _FH_1 _FH_2 _FH_3))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int) (_FH_3 Int) (|_FH_3'| Int)) (=> (and (>= _FH_2 3000) (>= _FH_1 2000) (= |_FH_0'| (+ _FH_0 1)) (>= _FH_0 1000) (= |_FH_3'| (+ _FH_3 1)) (= |_FH_2'| (+ _FH_2 1)) (= |_FH_1'| (+ _FH_1 1)) (inv_3 _FH_0 _FH_1 _FH_2 _FH_3)) (inv_3 |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int) (_FH_3 Int)) (=> (and (>= _FH_2 3000) (distinct _FH_0 _FH_3) (inv_3 _FH_0 _FH_1 _FH_2 _FH_3)) false)))

(check-sat)
