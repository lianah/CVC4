; COMMAND-LINE: --incremental --fmf-fun
(set-logic ALL_SUPPORTED)
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(define-fun-rec sum ((l Lst)) Int (ite (is-nil l) 0 (+ (head l) (sum (tail l)))))

(declare-fun input () Int)
(declare-fun p () Bool)
(declare-fun acc () Lst)
(assert (and (= acc (ite (>= input 0) (cons input nil) nil))
             (= p (>= (sum acc) 0))))


; EXPECT: unsat
(push 1)
(assert (not p))
(check-sat)
(pop 1)

; EXPECT: unsat
(push 1)
(assert (not p))
(check-sat)
(pop 1)


