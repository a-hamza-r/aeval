
(declare-rel fail12 ())
(declare-rel inv12 (Int Int Int Int Int Int))

(declare-var _v1_x Int)
(declare-var _v1_y Int)
(declare-var _v1_i Int)
(declare-var _v1_x1 Int)
(declare-var _v1_y1 Int)
(declare-var _v1_i1 Int)

(declare-var _v2_x Int)
(declare-var _v2_y Int)
(declare-var _v2_i Int)
(declare-var _v2_x1 Int)
(declare-var _v2_y1 Int)
(declare-var _v2_i1 Int)

(rule (=> (and 
	(= _v1_x 0)
	(= _v1_y 100)
	(= _v1_i 0)
	(= _v2_x 0)
	(= _v2_y 100)
	(= _v2_i 0)) 
	(inv12 _v1_x _v1_y _v1_i _v2_x _v2_y _v2_i)))
(rule (=> (and
	(inv12 _v1_x _v1_y _v1_i _v2_x _v2_y _v2_i)
	(< _v1_i 100)
	(= _v1_x1 (+ _v1_x 2))
	(= _v1_y1 (+ _v1_y 1))
	(= _v1_i1 (+ _v1_i 1))
	(< _v2_i 100)
	(= _v2_x1 (+ _v2_x 4))
	(= _v2_y1 (+ _v2_y 2))
	(= _v2_i1 (+ _v2_i 2)))
	(inv12 _v1_x1 _v1_y1 _v1_i1 _v2_x1 _v2_y1 _v2_i1)))
(rule (=> (and
	(inv12 _v1_x _v1_y _v1_i _v2_x _v2_y _v2_i)
	(>= _v1_i 100)
	(>= _v2_i 100)
	(not (= _v1_x _v2_x)) 
	(not (= _v1_y _v2_y)))
	fail12))
(query fail12)


;(rule (=> (and											rule #4 below
;	(inv12 _v1_x _v1_y _v1_i _v2_x _v2_y _v2_i)
;	(< _v1_i 100)
;	(= _v1_x1 (+ _v1_x 2))
;	(= _v1_y1 (+ _v1_y 1))
;	(= _v1_i1 (+ _v1_i 1))
;	(= _v2_x 0)
;	(= _v2_y 100)
;	(= _v2_i 0))
;	(inv12 _v1_x1 _v1_y1 _v1_i1 _v2_x _v2_y _v2_i)))
;(rule (=> (and											rule #3 below
;	(inv12 _v1_x _v1_y _v1_i _v2_x _v2_y _v2_i)
;	(< _v2_i 100)
;	(= _v2_x1 (+ _v2_x 4))
;	(= _v2_y1 (+ _v2_y 2))
;	(= _v2_i1 (+ _v2_i 2))
;	(= _v1_x 0)
;	(= _v1_y 100)
;	(= _v1_i 0))
;	(inv12 _v1_x _v1_y _v1_i _v2_x1 _v2_y1 _v2_i1)))

;	true -> t12
;	t12 -> _v1_inv*_v2_inv (_v1_0', _v1_1', _v1_2', _v2_0', _v2_1', _v2_2') 
;	t1 ^ _v1_inv*_v2_inv (_v1_0', _v1_1', _v1_2', _v2_0, _v2_1, _v2_2) -> _v1_inv*_v2_inv (_v1_0', _v1_1', _v1_2', _v2_0', _v2_1', _v2_2') 
;	t2 ^ _v1_inv*_v2_inv (_v1_0, _v1_1, _v1_2, _v2_0', _v2_1', _v2_2') -> _v1_inv*_v2_inv (_v1_0', _v1_1', _v1_2', _v2_0', _v2_1', _v2_2') 
;	_v1_inv*_v2_inv (_v1_0, _v1_1, _v1_2, _v2_0, _v2_1, _v2_2) -> _v1_inv*_v2_inv (_v1_0', _v1_1', _v1_2', _v2_0', _v2_1', _v2_2')
;	_v1_inv*_v2_inv (_v1_0, _v1_1, _v1_2, _v2_0, _v2_1, _v2_2) -> _v1_fail*_v2_fail