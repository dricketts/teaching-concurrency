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
// The algorithm is specified with an Init which specifies the initial
// state of the system and a Proc method which specifies the above instructions
// and has some assertions after each yield to prove correctness.
//
// Unlike in all other tools I've tried (TLA+, Dafny, Mypyvy), it wasn't
// necessary to record the control state of each process in a variable.
// Instead, I only record a boolean for each process, indicating whether
// that process has completed. This surprised me because the inductive
// invariant requires recording that if a process has completed the x
// update, its value of x is equal to 1. I weakened this part of the
// inductive invariant to just say that if a process has finished, then
// its value of x is equal to 1. I think CIVL is able to handle this weaker
// inductive invariant because I added an assertion that x[i] == 1 after
// the yield following the x update step. This seems to be, in some sense,
// a local way of recording the information that is missing from the
// inductive invariant. So the inductive invariant is spread between the
// predicate I've named ind_inv and this local assertion. As far as I can tell,
// this is the only fundamentally different proof of this algorithm in the
// different tools that I've tried.
//
// One shouldn't take the above discussion too seriously. I don't really
// understand CIVL, so I'm not sure if I've really specified/verified what
// I think I have.
//
// As with the Dafny solution, there is no scheduler method that actually
// calls Init and Proc, so there's no complete verification result, only
// an implicit one. I suspect that it's possible to write such a scheduler,
// but I don't know enough about CIVL to do so.

// Number of processes in the algorithm. There needs to be at least one.
const N : int;
axiom N >= 1;

var {:layer 0} x : [int]int;
var {:layer 0} y : [int]int;
// Records whether or not a process has finished.
var {:layer 0} done : [int]bool;

// Initial state of the system
procedure {:layer 0} Init()
ensures ind_inv(done, y, x);
modifies done, y, x;
{
	// Only the initial value of pc matters.
  done := (lambda i: int :: false);
	// Convince boogie that at least one process is not done.
  assert !done[0];
}

// The specification of a process, along with post-yield
// assertions necessary to conclude ind_inv.
procedure {:yields}	{:layer 0} Proc(i: int)
requires {:layer 0} ind_inv(done, y, x);
ensures {:layer 0} ind_inv(done, y, x);	
{
  call update_x(i);
	yield;
	assert {:layer 0} x[i] == 1;
	assert {:layer 0} x_inv(done, x);
	assert {:layer 0} safety(done, y);

	call update_y(i);
	call mark_done(i);
	yield;
	assert {:layer 0} x_inv(done, x);
	assert {:layer 0} safety(done, y);	
}

// CIVL doesn't seem to allow updates of global variables
// within yielding procedures, so I have to put these
// updates in non-yielding procedures.
procedure {:layer 0} update_x(i: int)
modifies x;
ensures x == old(x)[i:=1];
{
	x := x[i:=1];
}	

procedure {:layer 0} update_y(i: int)
modifies y;
ensures y == old(y)[i:=(old(x)[(i-1) mod N])];
{
	y := y[i:=(x[(i-1) mod N])];
}

procedure {:layer 0} mark_done(i: int)
modifies done;
ensures done == old(done)[i:=true];
{
  done := done[i:=true];
}	

// Whether or not an int i indicates an actual process
function in_range(i: int): bool
{
	0 <= i && i < N
}	

// The core correctness property of the system. If all the processes
// have finished, there's at least one element of y equal to 1.
function safety(done: [int]bool, y: [int]int): bool
{
	(forall i : int :: in_range(i) ==>  done[i]) ==>
	(exists i : int :: (in_range(i) && y[i] == 1))
}

// Records that all completed processes have their x equal to 1.
// This is weaker than than to corresponding inductive invariant
// conjunct in other tools for the same algorithm.
function x_inv(done: [int]bool, x: [int]int): bool
{
	(forall i : int :: (in_range(i) && done[i]) ==>  x[i] == 1)
}

// Inductive invariant. Given the discussion at the top of this file,
// this should probably be considered part of the global inductive
// invariant. I think the assert x[i] == 1 in Proc is also, in some sense,
// part of the global inductive invariant.
function ind_inv(done: [int]bool, y: [int]int, x: [int]int): bool
{
  safety(done, y) && x_inv(done, x)
}
