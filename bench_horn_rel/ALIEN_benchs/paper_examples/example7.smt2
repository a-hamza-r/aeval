(declare-fun vm () Int)
(declare-fun vl () Int)

(assert (forall ((M Int) (X Int)) (=> (and (= M X) (> vm 0) (>= vl 0)) (= (- (+ (* 2 M) 1) vl) (* vm X)))))

(check-sat)
(get-model)
