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
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma AbsIntTriangle(a: int, b: int)
  ensures AbsInt(a - b) <= AbsInt(a) + AbsInt(b)
{
}

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= 24 * AbsInt(n) + 250
{
  var c5, s5 := C2286(n, 5);
  var c6, s6 := C2286(n, 6);
  var c7, s7 := C2286(n, 7);
  AbsIntTriangle(n, 5);
  AbsIntTriangle(n, 6);
  AbsIntTriangle(n, 7);
  output := IntToString(c5 + c6 + c7);
  steps := s5 + s6 + s7 + 3;   // two additions (2) + IntToString (1)
}

method C2286(n: int, k: int) returns (r: int, ghost steps: nat)
  ensures steps <= 4 * AbsInt(n) + 4 * AbsInt(k) + 4 * AbsInt(n - k) + 14
{
  var fn, sfn := Fac2286(n);
  var fk, sfk := Fac2286(k);
  var fnk, sfnk := Fac2286(n - k);
  r := fn / (fk * fnk);
  steps := sfn + sfk + sfnk + 2;   // one multiplication + one division
}

method Fac2286(x: int) returns (p: int, ghost steps: nat)
  ensures p >= 1
  ensures steps <= 4 * AbsInt(x) + 4
{
  p := 1;
  var i := 2;
  steps := 1;
  while i <= x
    invariant p >= 1
    invariant i >= 2
    invariant steps <= 1 + 4 * (i - 2)
    invariant i <= (if x >= 2 then x + 1 else 2)
    decreases x - i
  {
    p := p * i;
    i := i + 1;
    steps := steps + 4;   // multiplication (1) + increment (1) + comparison/loop overhead (2)
  }
}
