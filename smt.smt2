; SMT.  Run with Z3; e.g.
;   $ z3 -t:10000 smt.smt2
; Expected output is
;   sat
;   unsat
; ("Unknown" for the first line is also legal.)

; Core types.
(define-sort ProcessID () Int)
(declare-datatypes ((PCLocation 0)) ((SetX SetY Done)))

; Number of processes.
(declare-const N Int)
(assert (> N 0))

; An int is a valid process ID if it is in the range [0, N).
(define-fun is-pid ((pid Int)) Bool (and (>= pid 0) (< pid N)))

; Chain of states.  See also: "Induction axiom for states" below.
(declare-sort StateNum)
(declare-const InitState StateNum)
(declare-fun next-state (StateNum) StateNum)

; Mutable state.
(declare-fun x (StateNum Int) Int) ; (x s i) is x[i] in state s
(declare-fun y (StateNum Int) Int) ; (y s i) is y[i] in state s
(declare-fun pc (StateNum ProcessID) PCLocation) ; (pc s p) is pc for process p in state s

; initial state:
;  x and y unconstrained
;  pc[*] = SetX
(assert (forall ((p ProcessID))
    (=> (is-pid p)
        (= (pc InitState p) SetX))))

; next relation:
;  SetX: x[pid] = 1
;  SetY: y[pid] = x[(i-1) mod N]
(define-fun Next ((S StateNum) (T StateNum)) Bool
    (or

        ; Stuttering: no change.  This is not optional; see "Next relation
        ; relates successive states" below.
        (and
            (forall ((i Int)) (= (x T i) (x S i)))
            (forall ((i Int)) (= (y T i) (y S i)))
            (forall ((p ProcessID)) (=> (is-pid p) (= (pc T p) (pc S p)))))

        ; "Real" state changes: some process (pid) acts.
        (exists ((pid ProcessID)) (and (is-pid pid) (or

            (and
                (= (pc S pid) SetX)
                (= (pc T pid) SetY)
                (forall ((i Int)) (= (x T i) (ite (= i pid) 1 (x S i))))
                (forall ((i Int)) (= (y T i) (y S i)))
                (forall ((p ProcessID)) (=> (and (is-pid p) (not (= p pid))) (= (pc T p) (pc S p)))))

            (and
                (= (pc S pid) SetY)
                (= (pc T pid) Done)
                (forall ((i Int)) (= (x T i) (x S i)))
                (forall ((i Int)) (= (y T i) (ite (= i pid) (x S (mod (- i 1) N)) (y S i))))
                (forall ((p ProcessID)) (=> (and (is-pid p) (not (= p pid))) (= (pc T p) (pc S p)))))

        )))
    ))

; Next relation relates successive states.  (Without stuttering, this axiom is
; unsatisfiable.  This axiom requires an infinite chain of states, and our
; algorithm stops making progress after a finite number of steps.)
(assert (forall ((S StateNum))
    (Next S (next-state S))))

; correctness:
;  once all processes have finished, y[j] = 1 for some j
(define-fun Correct ((S StateNum)) Bool
    (=> (forall ((p ProcessID)) (=> (is-pid p) (= (pc S p) Done)))
        (exists ((j ProcessID)) (and (is-pid j) (= (y S j) 1)))))

; inductive invariant:
;  for each process p that is in SetY or Done, x[p] = 1
(define-fun IndInv ((S StateNum)) Bool
    (and
        (Correct S)
        (forall ((p ProcessID)) (=> (is-pid p) (=> (or (= (pc S p) SetY) (= (pc S p) Done)) (= (x S p) 1))))))

; Induction axiom for states.  We could use integers for states and exploit
; induction on the naturals to avoid this axiom, but:
;  (1) Z3 can't prove inductive facts, no matter how obvious, so it won't work
;      with the Z3 solver.
;  (2) Using an uninterpreted type will make any solver happier by keeping the
;      "state" type separate from unrelated integer terms.
;  (3) This axiom is straightforward enough that I trust it.
(assert
    (=>
        (and
            (IndInv InitState)
            (forall ((S StateNum)) (=> (IndInv S) (IndInv (next-state S)))))
        (forall ((S StateNum)) (IndInv S))))

; Ensure our system description is consistent.  This should be SAT or UNKNOWN.
; An UNSAT result means our system is trivially unsatisfiable, and we made a
; mistake.  (You should probably run the solver with a timeout to ensure that
; you get UNKNOWN even when the solver would run forever.  For instance, run
; Z3 with the flag "-t:10000".)
(check-sat)

; final correctness check:
;  assert not correct and look for counterexample
(push)
    (assert (not (forall ((S StateNum)) (Correct S))))
    (check-sat)
(pop)
