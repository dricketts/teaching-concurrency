------------------------ MODULE TeachingConcurrency ------------------------
(***************************************************************************)
(* This is a specification of a simple concurrent algorithm from the paper *)
(* "Teaching Concurrency" by Leslie Lamport.  In there are N processes and *)
(* two arrays of length N, x and y.  Each process i executes the following *)
(* sequence of statements:                                                 *)
(*                                                                         *)
(*     x[i] := 1;                                                          *)
(*     y[i] := x[(i-1) mod N];                                             *)
(*                                                                         *)
(* The reads and writes of each x[j] are assumed to be atomic.  This       *)
(* algorithm has the property that once all processes have finished, at    *)
(* least one y[j] == 1.                                                    *)
(*                                                                         *)
(* Specifing this algorithm in PlusCal was straightforward.  Doing this    *)
(* proof suggested that the backend provers don't have good support for    *)
(* mod, so I changed that expression to the if-then-else expression below. *)
(***************************************************************************)

EXTENDS Integers, Naturals, TLAPS
CONSTANTS N
ASSUME N_Pos == N \in Nat \ {0}

(*
--algorithm Concurrency
{
    variables
        x \in [1..N -> Int],
        y \in [1..N -> Int];

    process (P \in 1..N)
    {
        s1: x[self] := 1;
        \* Poor support in the prover for % operator
        s2: y[self] := x[IF self = 1 THEN N ELSE self - 1];
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ x \in [1..N -> Int]
        /\ y \in [1..N -> Int]
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ x' = [x EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ y' = y

s2(self) == /\ pc[self] = "s2"
            /\ y' = [y EXCEPT ![self] = x[IF self = 1 THEN N ELSE self - 1]]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ x' = x

P(self) == s1(self) \/ s2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..N: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Core safety property. If every process has finished, at least
\* one element of y is equal to 1.
Safety == (\A p \in ProcSet : pc[p] = "Done") => \E p \in ProcSet : y[p] = 1

\* Simple type invariant
TypeOK ==
    /\ x \in [ProcSet -> Int]
    /\ y \in [ProcSet -> Int]
    /\ pc \in [ProcSet -> {"s1", "s2", "Done"}]

\* Inductive invariant. Requires additional conjunct recording that
\* after a process completes the x update statement, its element of
\* x is equal to 1.
IndInv ==
    /\ Safety
    /\ TypeOK
    /\ \A p \in ProcSet : pc[p] \in {"s2", "Done"} => x[p] = 1

\* Inductive invariance proof
THEOREM Spec => []IndInv
<1>1. Init => IndInv
   <2>1. ProcSet # {}
     BY N_Pos DEF ProcSet
   <2>2. QED
     BY <2>1 DEF IndInv, Safety, Init, TypeOK, ProcSet
<1>2. IndInv /\ [Next]_vars => IndInv'
  <2> SUFFICES ASSUME IndInv,
                      [Next]_vars
               PROVE  IndInv'
    OBVIOUS
  <2>1. ASSUME NEW self \in 1..N,
               s1(self)
        PROVE  IndInv'
    BY <2>1 DEF s1, ProcSet, IndInv, Safety, TypeOK
  <2>2. ASSUME NEW self \in 1..N,
               s2(self)
        PROVE  IndInv'
    BY N_Pos, <2>2 DEF s2, ProcSet, IndInv, Safety, TypeOK
  <2>3. CASE Terminating
    BY <2>3 DEF Terminating, vars, ProcSet, IndInv, Safety, TypeOK
  <2>4. CASE UNCHANGED vars
    BY <2>4 DEF vars, ProcSet, IndInv, Safety, TypeOK
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Next, P
<1>3. QED
    BY <1>1, <1>2, PTL DEF Spec
=============================================================================
