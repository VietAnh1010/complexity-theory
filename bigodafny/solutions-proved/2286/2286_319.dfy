// 630_F. Selection of Personnel  (problem 2286, solution 2286_319)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def fac(x):
// 	p = 1
// 	for i in range(2, x + 1):
// 		p *= i
// 	return p
//
//
// def c(n, k):
// 	return fac(n) // (fac(k) * fac(n - k))
//
// n = int(input())
// print(c(n, 5) + c(n, 6) + c(n, 7))
//
//
// --------------------------------------------------------------------
//
// PROOF NOTE (relation: tighter-costmodel). This proof gets O(n), strictly
// below the O(n**2) label. Fac2286 does n multiplications, each charged 1 by
// the stipulated cost table regardless of operand size, so the ghost bound
// is linear. CPython's `p *= i` is not O(1): p grows to n! and multiplying a
// k-digit bignum by a small int costs O(k), and the digit count of p after i
// steps is Theta(i*log(i)) -- so the true cost of the loop is
// sum_i O(i log i) = O(n^2 log n), which BigOBench's profiler rounded to
// O(n**2). The gap is exactly the excluded big-int cost, not a loose label.

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 7
  ensures steps <= 18 * n + 27
{
  var c5, s5 := C2286(n, 5);
  var c6, s6 := C2286(n, 6);
  var c7, s7 := C2286(n, 7);
  steps := s5 + s6 + s7;
  output := IntToString(c5 + c6 + c7);
  steps := steps + 3;
}

method C2286(n: int, k: int) returns (r: int, ghost steps: nat)
  requires n >= k >= 0
  ensures steps <= 6 * n + 8
{
  var fn, sfn := Fac2286(n);
  var fk, sfk := Fac2286(k);
  var fnk, sfnk := Fac2286(n - k);
  r := fn / (fk * fnk);
  steps := sfn + sfk + sfnk + 2;
}

method Fac2286(x: int) returns (p: int, ghost steps: nat)
  requires x >= 0
  ensures p >= 1
  ensures steps <= 3 * x + 2
{
  p := 1;
  var i := 2;
  steps := 2;
  while i <= x
    invariant p >= 1
    invariant i >= 2
    invariant i == 2 || i <= x + 1
    invariant steps <= 3 * (i - 2) + 2
    decreases x - i
  {
    p := p * i;
    i := i + 1;
    steps := steps + 3;
  }
}
