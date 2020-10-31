(set-logic HORN)
(declare-fun |inv12| (Int Int Int Int Int Int) Bool)

(assert (forall ((_pr_0 Int) (_pr_1 Int) (_pr_2 Int) (_pr_3 Int) (_pr_4 Int) (_pr_5 Int)) 
	(=> (and (= |_pr_0| 0) (= |_pr_1| 0) (>= |_pr_2| 0) (= |_pr_3| 0) (= |_pr_4| 0) (>= |_pr_5| 0)) 
	(|inv12| |_pr_0| |_pr_1| |_pr_2| |_pr_3| |_pr_4| |_pr_5|))))

(assert (forall ((_pr_0 Int) (_pr_1 Int) (_pr_2 Int) (_pr_3 Int) (_pr_5 Int) (_pr_0_ Int) (_pr_1_ Int) (_pr_2_ Int) (_pr_5_ Int) (_pr_3_ Int) (_pr_4_ Int) (_pr_4 Int)) 
(=> 
(and (|inv12| |_pr_0| |_pr_1| |_pr_2| |_pr_3| |_pr_4| |_pr_5|) (or (and (= _pr_0 0) (= _pr_1 0) (>= _pr_2 0) (< (+ _pr_3 (- _pr_5)) 0) (= (+ _pr_0 (- |_pr_0_|)) 0) (= (+ _pr_1 (- |_pr_1_|)) 0) (= (+ _pr_2 (- |_pr_2_|)) 0) (= (+ _pr_5 (- |_pr_5_|)) 0) (= (+ |_pr_3_| (- _pr_3) (- 1)) 0) (= (+ |_pr_4_| (- _pr_4) (- 2)) 0)) (and (= (+ _pr_2 (- |_pr_2_|)) 0) (= (+ _pr_5 (- |_pr_5_|)) 0) (= _pr_3 0) (= _pr_4 0) (>= _pr_5 0) (< (+ _pr_0 (- _pr_2)) 0) (= (+ |_pr_0_| (- 1) (- _pr_0)) 0) (= (+ |_pr_1_| (- 2) (- _pr_1)) 0) (= (+ _pr_3 (- |_pr_3_|)) 0) (= (+ _pr_4 (- |_pr_4_|)) 0) (distinct _pr_0 _pr_2)) (and (< (+ _pr_3 (- _pr_5)) 0) (= (+ _pr_2 (- |_pr_2_|)) 0) (= (+ _pr_5 (- |_pr_5_|)) 0) (= (+ |_pr_3_| (- _pr_3) (- 1)) 0) (= (+ |_pr_4_| (- _pr_4) (- 2)) 0) (< (+ _pr_0 (- _pr_2)) 0) (= (+ |_pr_0_| (- 1) (- _pr_0)) 0) (= (+ |_pr_1_| (- 2) (- _pr_1)) 0) (distinct _pr_0 _pr_2))))
(|inv12| |_pr_0_| |_pr_1_| |_pr_2_| |_pr_3_| |_pr_4_| |_pr_5_|))))

(assert (forall ((_pr_3 Int) (_pr_5 Int) (_pr_2 Int) (_pr_1 Int) (_pr_0 Int) (_pr_4 Int)) (=> (and 
(|inv12| |_pr_0| |_pr_1| |_pr_2| |_pr_3| |_pr_4| |_pr_5|) (= (+ _pr_3 (- _pr_5)) 0) (distinct _pr_1 (* 2 _pr_0)) (distinct (+ _pr_3 _pr_4) (* 3 _pr_3))) false)))

(check-sat)
