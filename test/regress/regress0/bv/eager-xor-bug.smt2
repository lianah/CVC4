(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 14))
(declare-fun v1 () (_ BitVec 14))
(declare-fun v2 () (_ BitVec 14))
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (xor a (xor b c)))
;; (assert (xor (not b) (not a)))
(assert (or a b))
;; (assert (= (bvxor v1 (bvxor v2 v3) (_ bv0 14))))
;; (assert (= (bvxor v1 (bvnot v2) (_ bv1 14))))
(check-sat)
