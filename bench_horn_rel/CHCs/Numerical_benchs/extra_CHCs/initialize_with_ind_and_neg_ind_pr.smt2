(declare-var i1 Int )
(declare-var _v1_i Int )
(declare-var _v1_i1 Int )
(declare-var _v1_len Int )
(declare-var _v1_array (Array Int Int))
(declare-var _v1_array1 (Array Int Int))
(declare-var _v2_i Int )
(declare-var _v2_i1 Int )
(declare-var _v2_len Int )
(declare-var _v2_array (Array Int Int))
(declare-var _v2_array1 (Array Int Int))
(declare-rel _v1_loop*_v2_loop (Int (Array Int Int) Int Int (Array Int Int) Int))
(declare-rel _v1_exit*_v2_exit ())

(rule (=> 
	(and 
		(= _v1_i 0)
		(= _v2_i 0)
		(>= _v1_len 0)
		(>= _v2_len 0)
		(= _v1_array _v2_array)		; pre
		(= _v1_len _v2_len)			; pre
	)
	(_v1_loop*_v2_loop _v1_i _v1_array _v1_len _v2_i _v2_array _v2_len)
))

(rule (=> 
	(and 
		(_v1_loop*_v2_loop _v1_i _v1_array _v1_len _v2_i _v2_array _v2_len)
		
		(= _v1_array1 (store _v1_array _v1_i _v1_i))
		(= _v1_i1 (+ _v1_i 1))
		(< _v1_i _v1_len)

		(= _v2_array1 (store _v2_array _v2_i (- _v2_i)))
		(= _v2_i1 (+ _v2_i 1))
		(< _v2_i _v2_len)
	)
	(_v1_loop*_v2_loop _v1_i1 _v1_array1 _v1_len _v2_i1 _v2_array1 _v2_len)
))

(rule (=> 
	(and 
		(_v1_loop*_v2_loop _v1_i _v1_array _v1_len _v2_i _v2_array _v2_len)
		
		(>= _v1_i _v1_len)
		(>= _v2_i _v2_len)

		(>= i1 0)														; post
		(< i1 _v1_len)													; post
		(not (= (+ (select _v1_array i1) (select _v2_array i1)) 0))		; post
	)
	_v1_exit*_v2_exit
))

(query _v1_exit*_v2_exit)



;(>= _v1_i1 0)
;(< _v1_i1 _v1_len)
;(not (= (select _v1_array _v1_i1) 1))
;(>= _v2_i1 0)
;(< _v2_i1 _v2_len)
;(not (= (select _v2_array _v2_i1) 1))