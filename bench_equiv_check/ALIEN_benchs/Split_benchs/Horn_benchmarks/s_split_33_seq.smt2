(declare-fun inv_0 (Int Int Int) Bool)
(declare-fun inv_1 (Int Int Int) Bool)

(assert (forall ((|_FH_0'| Int) (|_FH_1'| Int) (|_FH_2'| Int)) (=> (and (= 0 |_FH_0'|) (= 0 |_FH_1'|) (= 0 |_FH_2'|)) (inv_0 |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int)) (=> (and (= |_FH_1'| (mod (+ _FH_1 1) 100)) (= |_FH_0'| (+ _FH_0 1)) (= (div _FH_2 100) (div |_FH_0'| 100)) (= |_FH_2'| (+ _FH_2 0)) (= (div _FH_2 100) (div (+ _FH_0 1) 100)) (inv_0 _FH_0 _FH_1 _FH_2)) (inv_0 |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int)) (=> (and (inv_0 _FH_0 _FH_1 _FH_2) (not (= (div _FH_2 100) (div (+ _FH_0 1) 100)))) (inv_1 _FH_0 _FH_1 _FH_2))))

(assert (forall ((_FH_0 Int) (|_FH_0'| Int) (_FH_1 Int) (|_FH_1'| Int) (_FH_2 Int) (|_FH_2'| Int)) (=> (and (= |_FH_1'| (mod (+ _FH_1 1) 100)) (= |_FH_0'| (+ _FH_0 1)) (= |_FH_2'| (+ _FH_2 100)) (distinct (div _FH_2 100) (div |_FH_0'| 100)) (distinct (div _FH_2 100) (div (+ _FH_0 1) 100)) (inv_1 _FH_0 _FH_1 _FH_2)) (inv_1 |_FH_0'| |_FH_1'| |_FH_2'|))))

(assert (forall ((_FH_0 Int) (_FH_1 Int) (_FH_2 Int)) (=> (and (distinct _FH_0 (+ _FH_1 _FH_2)) (inv_1 _FH_0 _FH_1 _FH_2)) false)))

(check-sat)
