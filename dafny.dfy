// This is a specification of a simple concurrent algorithm from the paper
// "Teaching Concurrency" by Leslie Lamport. In there are N processes and
// two arrays of length N, x and y. Each process i executes the following
// sequence of statements:
//
//     x[i] := 1;
//     y[i] := x[(i-1) mod N];
//
// The reads and writes of each x[j] are assumed to be atomic. This
// algorithm has the property that once all processes have finished, at
// least one y[j] == 1.
//
// Dafny has no primitive notion of concurrency. One option is to use
// the approach described in "Modeling Concurrency in Dafny" by Rustan
// Leino [*], which is also how this algorithm would be modeled in TLA+.
// However, I wanted to see if the algorithm could be modeled in a way
// that preserves the simple sequential structure of each process. This
// doesn't really matter for such a short and simple algorithm, but might
// help when specifying algorithms in which processes have more control
// states.
//
// The main challenge is specifying what it means for a process to yield
// control to other processes after an atomic step. I believe that such a
// specification is only meaningful in the context of a desired correctness
// property and corresponding inductive invariant. We want it to be the case
// that each atomic step of a process preserves the inductive invariant,
// and from the perspective of a given process P, when P yields control, the
// state of the system can be modified arbitrarily as long as:
//     - the modification preserves the inductive invariant, and
//     - the modification preserves the control state of P
// I specified this with an unimplemented method Yield, which requires the
// inductive invariant as a precondition (enforcing that every atomic step
// preserves the inductive invariant), guarantees the inductive invariant
// as a post condition, and guarantees that the yielding process's control
// state doesn't change. This method, along with the algorithm and inductive
// invariant, are captured in the class below.
//
// A downside of this approach is that there is no way to model
// the scheduler in described in [*], so the methods Init and Proc
// are never called. This means that the scheduler is implicit, and
// there's no end to end verification argument.
//
// [*] http://leino.science/papers/krml260.pdf

// Possible control states of a process
datatype pc_label = x_pc | y_pc | done

class TeachingConcurrency {
    var pc: array<pc_label>;
    var x: array<int>;
    var y: array<int>;

    // The initial state of the system. This method doesn't actually
    // do anything. It simply verifies that constraints on the initial
    // state, as expressed by the requires clauses, imply the inductive
    // invariant. I could have expressed the constraint on pc as a while
    // loop or as a forall assignment statement. A while loop just seemed
    // more complicated than necessary, and a forall assignment statement
    // gave me some warning about triggers that I don't understand (because
    // I've been too lazy to read about triggers).
    method Init()
    requires pc.Length == x.Length == y.Length;
    requires forall i : int :: 0 <= i < pc.Length ==> pc[i] == x_pc;
    requires x != y
    requires 1 < pc.Length; // Non-empty set of processes.
    ensures IndInv();
    modifies pc;
    {
        // Need to convince Dafny of existence of a process
        assert pc[1] != done;
    }

    // Specification of a process. This requires explicitly updating
    // the control state (pc) of the process.
    method Proc(i: int)
    requires 0 <= i < pc.Length;
    requires IndInv();
    ensures IndInv();
    modifies x, y, pc;
    {
        x[i] := 1;
        pc[i] := y_pc;
        Yield(i);

        y[i] := x[(i - 1) % x.Length];
        pc[i] := done;
        // The following assertions convince Dafny that IndInv
        // holds. I couldn't figure out a simpler way to do so.
        assert x_Inv();
        assert AllDone() ==> x[(i - 1) % x.Length] == 1;
        assert AllDone() ==> y[i] == 1;
        Yield(i);
    }

    // All processes have finished.
    predicate AllDone()
    reads `pc, pc;
    {
        forall i : int :: 0 <= i < pc.Length ==> pc[i] == done
    }

    // The core correctness property of the algorithm. If every process
    // has finished, then at least one y[i] == 1.
    predicate Safety()
    requires pc.Length == y.Length;
    reads `pc, pc, `y, y;
    {
        AllDone() ==> exists i : int :: 0 <= i < y.Length && y[i] == 1
    }

    // Conjoining the following to Safety forms an inductive invariant.
    // x_Inv just records that a x[i] = 1 once a process has moved                                                                                
    // past x_pc.
    predicate x_Inv()
    requires pc.Length == x.Length;
    reads `pc, pc, `x, x;
    {
        forall i : int ::
            (0 <= i < pc.Length && pc[i] in {y_pc, done}) ==>
            x[i] == 1
    }

    // The full inductive invariant.
    predicate IndInv()
    reads `pc, pc, `x, x, `y, y;
    {
        x != y && pc.Length == x.Length == y.Length &&
        Safety() && x_Inv()
    }

    method Yield(i: int)
    requires 0 <= i < pc.Length;
    requires IndInv();
    ensures IndInv();
    ensures pc[i] == old(pc[i]);
    modifies pc, x, y;
}
