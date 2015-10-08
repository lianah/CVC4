(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun v0 () (_ BitVec 2))
(declare-fun v1 () (_ BitVec 2))
(assert (and
	 (= (concat v0 v1) (concat v1 v0))
	 (not (= v0 v1))))
(check-sat)
(exit)
