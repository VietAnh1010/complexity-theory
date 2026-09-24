// 633_A. Ebony and Ivory  (problem 1678, solution 1678_68)
// time complexity: O(1)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import ceil
// def gcdEx(a,b,x,y):
//     if not a:
//         return 0,1,b
//     x1,y1,g=gcdEx(b%a,a,0,0)
//     x=y1-(b//a)*x1
//     y=x1
//     return x,y,g
// a,b,c=map(int, input().split())
// x,y,g=gcdEx(a,b,0,0)
// if c%g:
//     print("No")
// else:
//     x,y=x*c//g,y*c//g
//     k1=ceil(-x*g/b)
//     k2=(y*g)//a
//     c=abs(k2-k1+1)
//     print("Yes" if c>0 else "No")
// --------------------------------------------------------------------

include "../../../../prelude.dfy"
import opened Prelude

function GcdEx(a: int, b: int): (int, int, int)
  decreases if a < 0 then -a else a
{
  if a == 0 then (0, 1, b)
  else
    var r := GcdEx(b % a, a);
    (r.1 - (b / a) * r.0, r.0, r.2)
}

// Dafny's % is Euclidean, so b % a is in [0, a) for a > 0; induct on a.
lemma GcdExPos(a: int, b: int)
  requires a >= 0 && b > 0
  ensures GcdEx(a, b).2 > 0
  decreases a
{
  if a != 0 { GcdExPos(b % a, a); }
}

// The recursion count of GcdEx, mirroring its own recursive structure. This
// is not a size- or value-independent quantity: the recursive call is on
// b % a, which strictly decreases the FIRST argument, so the count is bounded
// by that argument's magnitude, not by a constant.
ghost function GcdExSteps(a: int, b: int): nat
  decreases if a < 0 then -a else a
{
  if a == 0 then 1 else 1 + GcdExSteps(b % a, a)
}

// A loose (non-tight) bound: recursion depth is at most a + 1 for a >= 0,
// because a strictly decreases (b % a < a for a > 0, by Dafny's Euclidean %)
// every step until it hits 0. The tight bound is O(log(min(a,b))) via a
// Fibonacci argument; this weaker linear bound is what a bounded proof
// reaches, and it is enough to show the recursion is NOT a constant.
lemma GcdExStepsBound(a: int, b: int)
  requires a >= 0
  ensures GcdExSteps(a, b) <= a + 1
  decreases a
{
  if a == 0 {
  } else {
    GcdExStepsBound(b % a, a);
  }
}

function CeilDiv(p: int, q: int): int
  requires q > 0
{
  -FloorDiv(-p, q)
}

// Instrumented copy. GcdEx's own recursion is charged its step count,
// GcdExSteps, bounded by GcdExStepsBound -- linear in `rows`, not constant.
method Solve(rows: int, columns: int, value: int) returns (output: string, ghost steps: nat)
  requires rows >= 1
  requires columns >= 1
  ensures steps <= rows + 15
{
  steps := 1;
  var a := rows;
  var b := columns;
  var c := value;
  var r := GcdEx(a, b);
  GcdExStepsBound(a, b);
  steps := steps + GcdExSteps(a, b);
  var x := r.0;
  var y := r.1;
  var g := r.2;
  GcdExPos(a, b);
  steps := steps + 1;
  if c % g != 0 {
    output := "No";
    steps := steps + 1;
  } else {
    var xp := FloorDiv(x * c, g);
    var yp := FloorDiv(y * c, g);
    var k1 := CeilDiv(-xp * g, b);
    var k2 := FloorDiv(yp * g, a);
    var cc := AbsInt(k2 - k1 + 1);
    output := if cc > 0 then "Yes" else "No";
    steps := steps + 7;
  }
}
