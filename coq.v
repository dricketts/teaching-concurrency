(*
This is a specification of a simple concurrent algorithm from the paper
"Teaching Concurrency" by Leslie Lamport. In there are N processes and
two arrays of length N, x and y. Each process i executes the following
sequence of statements:

     x[i] := 1;
     y[i] := x[(i-1) mod N];

The reads and writes of each x[j] are assumed to be atomic. This
algorithm has the property that once all processes have finished, at
least one y[j] == 1.
*)

Require Import Coq.Arith.PeanoNat.
Require Import Omega.

Section Problem.

(* N is the number of processes. *)
Parameter N : nat.

(* Processes are identified by natural numbers. A variable is a function
over all natural numbers, not just those from [0, N). However, the
definition of reachable below restricts updates to processes from [0, N) *)
Definition var (T : Set) := nat -> T.
Definition Proc (i : nat) := i < N.
(* There's at least one process. *)
Axiom Proc_0 : Proc 0.

(* Control state of a process. A process is at control
state assign_x if it has not started, assign_y if it has
executed its assignment to x but not to y, and done if it
has finished. *)
Inductive pc_label :=
| assign_x
| assign_y
| done.

(* State of the system. *)
Record state : Set := mkState
{ pc : var pc_label
; x  : var nat
; y  : var nat
}.

(* Update the pc value of a single process *)
Definition update_pc (st : state) (i : nat) (l : pc_label) : state :=
    {|pc := fun j => if Nat.eq_dec i j then l else st.(pc) j
    ; x := st.(x)
    ; y := st.(y)|}.

(* Update the x value of a single process *)
Definition update_x (st : state) (i : nat) (v : nat) : state :=
    {|pc := st.(pc)
    ; x := fun j => if Nat.eq_dec i j then v else st.(x) j
    ; y := st.(y)|}.

(* Update the y value of a single process *)
Definition update_y (st : state) (i : nat) (v : nat) : state :=
    {|pc := st.(pc)
    ; x := st.(x)
    ; y := fun j => if Nat.eq_dec i j then v else st.(y) j|}.

(* Set of reachable states *)
Inductive reachable : state -> Prop :=
| init : forall init_x init_y, reachable
    {|pc := fun _ => assign_x; x := init_x; y := init_y |}
| x_step : forall st, reachable st ->
    forall i, Proc i -> st.(pc) i = assign_x ->
        reachable (update_x (update_pc st i assign_y) i 1)
| y_step : forall st, reachable st ->
        forall i, Proc i -> st.(pc) i = assign_y ->
            let j := if Nat.eq_dec (i + 1) N then 0 else i + 1 in
            reachable (update_y (update_pc st i done) i (st.(x) j))
.

(* Property we want to prove: if every process is done, at least
one process has y[i] = 1. *)
Definition safe st :=
    (forall i, Proc i -> st.(pc) i = done) ->
    exists i, Proc i /\ st.(y) i = 1.

(* Inductive invariant. Adds to safe an invariant tracking the value
of x. *)
Definition indinv st :=
    safe st /\
    forall i, Proc i ->
        (st.(pc) i = assign_y \/ st.(pc) i = done) ->
        st.(x) i = 1.

Lemma Proc_mod :
    forall i, Proc i -> Proc (if Nat.eq_dec (i + 1) N then 0 else i + 1).
Proof.
    intros. destruct (Nat.eq_dec (i + 1) N).
    - apply Proc_0.
    - unfold Proc in *. omega.
Qed.

Lemma reachable_indinv :
    forall st, reachable st -> indinv st.
Proof.
    intros st Hreach. induction Hreach.
    - split; simpl.
        { intro. specialize (H 0 Proc_0). discriminate. }
        { intros. destruct H0; discriminate. }
    - split; simpl.
        { unfold safe. intros. specialize (H1 i H). simpl in H1.
          destruct (Nat.eq_dec i i); try discriminate; intuition. }
        { intros. destruct (Nat.eq_dec i i0); auto. unfold indinv in IHHreach.
          apply IHHreach; auto. }
    - split; simpl.
        { unfold indinv, safe in *. intros.
          exists i; split; auto.
          assert (Proc j) as HProcj by (unfold j; apply Proc_mod; auto).
          assert (x st j = 1).
          { destruct IHHreach as [_ IHHreach]. apply IHHreach; auto.
            specialize (H1 j HProcj). simpl in *.
            destruct (Nat.eq_dec i j); auto. rewrite <- e. auto. }
          simpl. destruct (Nat.eq_dec i i); intuition. }
        { intros. destruct IHHreach as [_ IHHreach]. apply IHHreach; auto.
          destruct (Nat.eq_dec i i0); auto. rewrite <- e. auto. }
Qed.

Theorem reachable_safe :
    forall st, reachable st -> safe st.
Proof.
    apply reachable_indinv.
Qed.

End Problem.