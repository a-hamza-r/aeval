; K = 2
; Transition relation
(define-fun T ((%init Bool) ($x$0 Int) ($state$0 Int) ($bias$0 Int) ($guarantee1$0 Bool) ($guarantee2$0 Bool) ($guarantee3$0 Bool) ($guarantee4$0 Bool) ($guarantee5$0 Bool) ($guarantee_all$0 Bool) ($bias_max$0 Bool) ($x$1 Int) ($state$1 Int) ($bias$1 Int) ($guarantee1$1 Bool) ($guarantee2$1 Bool) ($guarantee3$1 Bool) ($guarantee4$1 Bool) ($guarantee5$1 Bool) ($guarantee_all$1 Bool) ($bias_max$1 Bool)) Bool (and (= $bias$1 (ite %init 0 (+ (ite (= $x$1 1) 1 (- 0 1)) $bias$0))) (= $bias_max$1 (ite %init false (or (or (>= $bias$1 2) (<= $bias$1 (- 0 2))) $bias_max$0))) (= $guarantee1$1 (=> (= $state$1 0) (= $bias$1 0))) (= $guarantee2$1 (ite %init true (=> (and (= $state$0 0) (= $x$1 1)) (= $state$1 2)))) (= $guarantee3$1 (ite %init true (=> (and (= $state$0 0) (= $x$1 0)) (= $state$1 1)))) (= $guarantee4$1 (=> $bias_max$1 (= $state$1 3))) (= $guarantee5$1 (or (or (or (= $state$1 0) (= $state$1 1)) (= $state$1 2)) (= $state$1 3))) (= $guarantee_all$1 (and (and (and (and $guarantee1$1 $guarantee2$1) $guarantee3$1) $guarantee4$1) $guarantee5$1)) (or (= $x$1 0) (= $x$1 1))))
; Universally quantified variables
(declare-fun $x$~1 () Int)
(declare-fun $state$~1 () Int)
(declare-fun $bias$~1 () Int)
(declare-fun $guarantee1$~1 () Bool)
(declare-fun $guarantee2$~1 () Bool)
(declare-fun $guarantee3$~1 () Bool)
(declare-fun $guarantee4$~1 () Bool)
(declare-fun $guarantee5$~1 () Bool)
(declare-fun $guarantee_all$~1 () Bool)
(declare-fun $bias_max$~1 () Bool)
(declare-fun $x$0 () Int)
(declare-fun $state$0 () Int)
(declare-fun $bias$0 () Int)
(declare-fun $guarantee1$0 () Bool)
(declare-fun $guarantee2$0 () Bool)
(declare-fun $guarantee3$0 () Bool)
(declare-fun $guarantee4$0 () Bool)
(declare-fun $guarantee5$0 () Bool)
(declare-fun $guarantee_all$0 () Bool)
(declare-fun $bias_max$0 () Bool)
(declare-fun $x$1 () Int)
(declare-fun $state$3 () Int)
(declare-fun $bias$3 () Int)
(declare-fun $guarantee1$3 () Bool)
(declare-fun $guarantee2$3 () Bool)
(declare-fun $guarantee3$3 () Bool)
(declare-fun $guarantee4$3 () Bool)
(declare-fun $guarantee5$3 () Bool)
(declare-fun $guarantee_all$3 () Bool)
(declare-fun $bias_max$3 () Bool)
(assert (and (T false $x$0 $state$0 $bias$0 $guarantee1$0 $guarantee2$0 $guarantee3$0 $guarantee4$0 $guarantee5$0 $guarantee_all$0 $bias_max$0 $x$1 $state$3 $bias$3 $guarantee1$3 $guarantee2$3 $guarantee3$3 $guarantee4$3 $guarantee5$3 $guarantee_all$3 $bias_max$3) $guarantee_all$3))