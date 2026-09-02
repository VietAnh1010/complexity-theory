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
// 
// def c(i, j):
//   return fact(i) // (fact(j) * fact(i - j))
// 
// n = int(input())
// ans = 1
// for j in range(5):
//  ans *= n - j
// print(ans * c(n, 5))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Fact(i: int) returns (r: int)
{
  r := 1;
  var j := 1;
  while j <= i
    invariant j >= 1
    decreases i - j + 1
  {
    r := r * j;
    j := j + 1;
  }
}

method Comb(i: int, j: int) returns (r: int)
{
  var fi := Fact(i);
  var fj := Fact(j);
  var fij := Fact(i - j);
  var denom := fj * fij;
  if denom != 0 {
    r := FloorDiv(fi, denom);
  } else {
    r := 0;
  }
}

method Solve(n: int) returns (output: string)
{
  var ans := 1;
  var j := 0;
  while j < 5
    invariant 0 <= j <= 5
  {
    ans := ans * (n - j);
    j := j + 1;
  }
  var c := Comb(n, 5);
  output := IntToString(ans * c);
}
