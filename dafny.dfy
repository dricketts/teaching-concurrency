type pc_label = int

predicate Inv(pc: array<pc_label>, y: array<int>)
requires pc.Length == y.Length;
reads pc, y;
{
    (forall i : int :: 0 <= i < pc.Length ==> pc[i] == 2) ==>
    exists i : int :: 0 <= i < y.Length && y[i] == 1
}

predicate x_Inv(pc: array<pc_label>, x: array<int>)
requires pc.Length == x.Length;
reads pc, x;
{
    forall i : int ::
        (0 <= i < pc.Length && pc[i] in {1, 2}) ==>
        x[i] == 1
}

predicate IndInv(pc: array<pc_label>, x: array<int>, y: array<int>)
requires pc.Length == x.Length == y.Length;
reads pc, x, y;
{
    Inv(pc, y) && x_Inv(pc, x)
}

method Yield(i: int, pc: array<pc_label>, x: array<int>, y: array<int>)
requires pc.Length == x.Length == y.Length;
requires 0 <= i < pc.Length;
requires IndInv(pc, x, y);
ensures IndInv(pc, x, y);
ensures pc[i] == old(pc[i]) + 1;
modifies pc, x, y;

method Proc(i: int, pc: array<pc_label>, x: array<int>, y: array<int>)
requires pc.Length == x.Length == y.Length;
// requires pc != x; <- This doesn't seem to be necessary.
requires pc != y;
requires x != y;
requires 0 <= i < pc.Length;
requires pc[i] == 0;
requires IndInv(pc, x, y);
ensures IndInv(pc, x, y);
modifies x, y, pc;
{
    x[i] := 1;
    Yield(i, pc, x, y);
    y[i] := x[(i - 1) % x.Length];
    assert pc[i] == 1; // Why is this assertion necessary?
    Yield(i, pc, x, y);
}

// IndInv didn't work first time
// Did assertion based debugging. Started with
// x_Inv and Inv immediately after x[i] := 1.
// Neither held, Inv was missing yield requires !done[i]
// (regular requires !done[i] had no effect).
// x_Inv still didn't hold.

// Problem with iterator stuff, asked on stack overflow, 
// gave up on getting that to work, realized if I'm not going
// to have main loop, no point in using iterators, might
// as well just have a method per process, and a method yield
// with IndInv as pre and post condition.

// Property held vacuously at first, because I wrote
// ensures pc[i] == old(pc)[i] + 1; instead of
// ensures pc[i] == old(pc[i]) + 1; in Yield. I guess
// the first one old(pc) is just a pointer to pc, which
// hasn't changed. I figured this issue out with assertion
// based debugging, eventually just putting an assert false in.
// I was initially suspicious because I modified x_Inv to
// something I believe to be insufficient (based on my
// experience with the TLAPS proof). In particular, I reduced
// the set of pc's under which x[i] == 1.

// Needed to add that pc, x, y are not equal. Does this express
// that the whole array is disjoint?

// Annoyingly, I need to add assertion pc[i] == 1 after y update
// (before y update doesn't help).