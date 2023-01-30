(declare-fun inv_0 (Int Int Int) Bool)
(declare-fun inv_1 (Int Int Int) Bool)
(declare-fun inv_2 (Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int)) (=> (and (= 0 |_FH_0'|) (= 3333 |_FH_1'|) (= 6666 |_FH_2'|)) (inv_0 |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int)) (=> (and (distinct _FH_0 9999) (< _FH_0 3333) (= |_FH_0'| (+ _FH_0 1)) (= |_FH_1'| (+ _FH_1 0)) (= |_FH_2'| (+ _FH_2 0)) (< _FH_1 6666) (inv_0 _FH_0 _FH_1 _FH_2)) (inv_0 |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int)) (=> (and (inv_0 _FH_0 _FH_1 _FH_2) (not (and (< _FH_0 3333) (< _FH_1 6666)))) (inv_1 _FH_0 _FH_1 _FH_2))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int)) (=> (and (distinct _FH_0 9999) (= |_FH_0'| (+ _FH_0 1)) (= |_FH_1'| (+ _FH_1 1)) (>= _FH_0 3333) (= |_FH_2'| (+ _FH_2 0)) (< _FH_1 6666) (inv_1 _FH_0 _FH_1 _FH_2)) (inv_1 |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int)) (=> (and (inv_1 _FH_0 _FH_1 _FH_2) (not (and (>= _FH_0 3333) (< _FH_1 6666)))) (inv_2 _FH_0 _FH_1 _FH_2))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int)) (=> (and (distinct _FH_0 9999) (>= _FH_1 6666) (= |_FH_0'| (+ _FH_0 1)) (= |_FH_1'| (+ _FH_1 1)) (>= _FH_0 3333) (= |_FH_2'| (+ _FH_2 1)) (inv_2 _FH_0 _FH_1 _FH_2)) (inv_2 |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int)) (=> (and (= 9999 _FH_0) (distinct _FH_2 9999) (inv_2 _FH_0 _FH_1 _FH_2)) false)))

(check-sat)
