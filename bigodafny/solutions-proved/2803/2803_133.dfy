// 630_H. Benches  (problem 2803, solution 2803_133)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def fact(i):
//   ans = 1
//   for j in range(1, i + 1):
//     ans *= j
//   return ans
// def c(i, j):
//   return fact(i) // (fact(j) * fact(i - j))
// n = int(input())
// ans = 1
// for j in range(5):
//  ans *= n - j
// print(ans * c(n, 5))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Fact(i: int) returns (r: int, ghost steps: nat)
  ensures steps <= 2 * AbsInt(i) + 4
{
  r := 1;
  steps := 1;
  var j := 1;
  while j <= i
    invariant j >= 1
    invariant j == 1 || j <= i + 1
    invariant steps == 2 * (j - 1) + 1
    decreases i - j + 1
  {
    r := r * j;
    j := j + 1;
    steps := steps + 2;
  }
  steps := steps + 1;
}

method Comb(i: int, j: int) returns (r: int, ghost steps: nat)
  ensures steps <= 2 * AbsInt(i) + 2 * AbsInt(j) + 2 * AbsInt(i - j) + 15
{
  var fi, s1 := Fact(i);
  var fj, s2 := Fact(j);
  var fij, s3 := Fact(i - j);
  var denom := fj * fij;
  steps := s1 + s2 + s3 + 2;
  if denom != 0 {
    r := FloorDiv(fi, denom);
  } else {
    r := 0;
  }
  steps := steps + 1;
}

// Every arithmetic op here is charged 1 regardless of the magnitude of the
// numbers (Dafny ints are arbitrary precision) -- so Fact(i) costs O(i), and
// Solve costs O(n), well inside the labelled O(n**2).
method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * AbsInt(n) + 2 * AbsInt(n - 5) + 37
{
  var ans := 1;
  var j := 0;
  steps := 1;
  while j < 5
    invariant 0 <= j <= 5
    invariant steps <= 2 * j + 1
  {
    ans := ans * (n - j);
    j := j + 1;
    steps := steps + 2;
  }
  var c, cSteps := Comb(n, 5);
  steps := steps + cSteps;
  output := IntToString(ans * c);
  steps := steps + 1;
}
