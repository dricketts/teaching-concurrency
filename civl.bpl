const N : int;
axiom N >= 1;

var {:layer 0} x : [int]int;
var {:layer 0} y : [int]int;
// ghost variable recording completion of
// a process. I don't see how to do this without
// such a variable.
var {:layer 0} done : [int]bool; 

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

function in_range(i: int): bool
{
	0 <= i && i < N
}	

function inv(done: [int]bool, y: [int]int): bool
{
	(forall i : int :: in_range(i) ==>  done[i]) ==>
	(exists i : int :: (in_range(i) && y[i] == 1))
}

function x_inv(done: [int]bool, x: [int]int): bool
{
	(forall i : int :: (in_range(i) && done[i]) ==>  x[i] == 1)
}

function ind_inv(done: [int]bool, y: [int]int, x: [int]int): bool
{
  inv(done, y) && x_inv(done, x)
}

procedure {:yields}	{:layer 0} run(i: int)
requires {:layer 0} ind_inv(done, y, x);
ensures {:layer 0} ind_inv(done, y, x);	
{
  call update_x(i);
	yield;
	assert {:layer 0} x[i] == 1;
	assert {:layer 0} x_inv(done, x);
	assert {:layer 0} inv(done, y);

	call update_y(i);
	call mark_done(i);
	assert {:layer 0} x_inv(done, x);
	assert {:layer 0} inv(done, y);
}

// Once I just added the done variable and encoded the inductive invariant
// and asserted it everywhere, everything just
// worked. Main downside is I can't figure out
// how to write a "main" procedure to get an
// end to end result. This is probably my own
// ignorance and a lack of documentation.
//
// The stated inductive invariant is split in a sense, relative
// to TLA+ - there's an assert (x[i] == 1) which is covered
// by pc[i] == "s2" => x[i] = 1 in the TLA+ inductive invariant.
//
// I generally wasn't sure what to do when something didn't get
// verified. In TLA+, I can just decompose the proof further.
// The analogous thing here seems to be adding assertions, but
// that's a flat approach, doesn't seem to allow decomposition.
// It's an unfair comparison because I have decent experience
// writing TLA+ proofs and almost no experience with CIVL. And,
// once I got the hang of assertion-based proof debugging, it
// worked out reasonably well for this simple example.
//
// Unlike TLAPS, there are counter example traces, but they mean
// nothing to me, so it is as good as no counter example.
//
// When I first started this proof, I tried to express only local
// assertions/contracts, but it wasn't clear how to do so. This
// problem seems to inherently requires some form of global
// reasoning.
// Example:
// - try a ghost variable to record value of x_left before the
//   y step (I wasn't sure what to do with this variable).
// - try ensure that either y[i] == 1 or left proc not done
//   (a form of global reasoning).
//
// Assertions within the program text was maybe a bit faster
// than in TLAPS, but it's hard to say how well that would scale
// to more complicated examples.
//
// One problem is that I don't really understand what get checked
// at each yield point.
//
// Annoying that I have to factor out update_x and update_y.

procedure {:yields}	{:layer 0} run_all(i: int)
requires {:layer 0} 0 <= i && i <= N;
requires {:layer 0} ind_inv(done, y, x);
ensures {:layer 0} ind_inv(done, y, x);
{
	if (i < N) {
		 par run(i) | run_all(i + 1);
	}
	yield;
}	

// Assertion based proof debugging kind of nice.
// Hard to say how it would work when more levels
// might be required.
procedure {:yields}	{:layer 0} main()
requires {:layer 0} (forall i : int :: in_range(i) ==>  !done[i]);
ensures {:layer 0} ind_inv(done, y, x);
{
	// Need this assertion, probably to prove
	// that there exists an i in_range.
  assert {:layer 0} in_range(0);
	call run_all(0);
//  par run(0);// | run(1);
	yield;
	assert {:layer 0}	ind_inv(done, y, x);
}	
