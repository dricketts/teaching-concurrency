------------------------ MODULE TeachingConcurrency ------------------------
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

Inv == (\A p \in ProcSet : pc[p] = "Done") => \E p \in ProcSet : y[p] = 1

TypeOK ==
    /\ x \in [ProcSet -> Int]
    /\ y \in [ProcSet -> Int]
    /\ pc \in [ProcSet -> {"s1", "s2", "Done"}]

IndInv ==
    /\ Inv
    /\ TypeOK
    /\ \A p \in ProcSet : pc[p] \in {"s2", "Done"} => x[p] = 1

(* Got stuck for a minute on Init => Inv because
   I was missing assumption N >= 1. I expected a contradiction
   to (\A p \in ProcSet : pc[p] = "Done"). Going one level
   down in the proof tree revealed that this requires ProcSet
   to be non-empty, which is implied by N >= 1. Going a level down
   made it easy to figure out what the prover couldn't prove.
   Update: in the end, the prover seemed quite sensitive to the precise
   form of this assumption when proving Init => IndInv, so I stated
   a separate step (ProcSet # {}), and then the rest of that proof works
   without any decomposition.

   Sometimes annoying not having procedural commands like in
   Coq, but much of this is mitigated with decompose proof command,
   which gets rid of tedious manipulations.

   Learned that TLAPS struggled with modulus operator. Changed
   to IF-THEN-ELSE, easy to re-run prover on everything to see
   what still holds. Status coloring nice.

   Lack of modulus reasoning annoying.

   Inductive invariant right first time, but I had done the problem
   before. Mostly spent time fighting with prover, but this
   is because I was missing the right assumption on N (an obvious one in
   retrospect). Decomposing proof into more levels made this
   process less painful.

   Nice proof debugging process: introduce earlier step, not prove it,
   see if helps with current step, then prove it to see problem, then
   fix issue (e.g. add assumption) and fold everything into current step
   and get rid of earlier step.

   Never used decompose proof command
*)

THEOREM Spec => []IndInv
<1>1. Init => IndInv
   <2>1. ProcSet # {}
     BY N_Pos DEF ProcSet
   <2>2. QED
     BY <2>1 DEF IndInv, Inv, Init, TypeOK, ProcSet
<1>2. IndInv /\ [Next]_vars => IndInv'
  <2> SUFFICES ASSUME IndInv,
                      [Next]_vars
               PROVE  IndInv'
    OBVIOUS
  <2>1. ASSUME NEW self \in 1..N,
               s1(self)
        PROVE  IndInv'
    BY <2>1 DEF s1, ProcSet, IndInv, Inv, TypeOK
  <2>2. ASSUME NEW self \in 1..N,
               s2(self)
        PROVE  IndInv'
    BY N_Pos, <2>2 DEF s2, ProcSet, IndInv, Inv, TypeOK
  <2>3. CASE Terminating
    BY <2>3 DEF Terminating, vars, ProcSet, IndInv, Inv, TypeOK
  <2>4. CASE UNCHANGED vars
    BY <2>4 DEF vars, ProcSet, IndInv, Inv, TypeOK
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Next, P
<1>3. QED
    BY <1>1, <1>2, PTL DEF Spec
=============================================================================
