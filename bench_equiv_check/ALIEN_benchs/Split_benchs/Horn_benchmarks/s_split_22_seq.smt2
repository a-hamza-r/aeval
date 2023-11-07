(declare-fun inv_0 (Int Int Int) Bool)
(declare-fun inv_1 (Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int)) (=> (and (= 0 |_FH_0'|) (= 767976 |_FH_1'|) (= 0 |_FH_2'|)) (inv_0 |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int)) (=> (and (= |_FH_1'| (+ _FH_1 (- 1))) (= |_FH_0'| (+ _FH_0 1)) (= |_FH_2'| (+ _FH_2 0)) (distinct (mod (+ _FH_0 (- _FH_1)) 3) 1) (inv_0 _FH_0 _FH_1 _FH_2)) (inv_0 |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int)) (=> (and (inv_0 _FH_0 _FH_1 _FH_2) (not (distinct (mod (+ _FH_0 (- _FH_1)) 3) 1))) (inv_1 _FH_0 _FH_1 _FH_2))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int)) (=> (and (= (mod (+ _FH_0 (- _FH_1)) 3) 1) (= |_FH_1'| (+ _FH_1 (- 1))) (= |_FH_0'| (+ _FH_0 1)) (= |_FH_2'| (+ _FH_2 3)) (inv_1 _FH_0 _FH_1 _FH_2)) (inv_1 |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int)) (=> (and (< _FH_2 280275) (>= _FH_0 280275) (inv_1 _FH_0 _FH_1 _FH_2)) false)))

(check-sat)
