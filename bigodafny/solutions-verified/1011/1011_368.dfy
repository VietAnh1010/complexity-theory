// 1099_B. Squares and Segments  (problem 1011, solution 1011_368)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # http://codeforces.com/contest/1099/problem/B
// n = int(input())
// a = b = 1
// while a * b < n:
//     if a < b:
//         a += 1
//     else:
//         b += 1
// 
// print(a+b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 1
  ensures steps <= 8 * n + 5
{
  steps := 1;
  var a := 1;
  var b := 1;
  while a * b < n
    invariant a >= 1 && b >= 1
    invariant steps <= 2 * (a * b) - 1
    invariant a * b <= 2 * n + 1
    decreases n - a * b
  {
    var oa, ob := a, b;
    if a < b {
      a := a + 1;
    } else {
      b := b + 1;
    }
    assert a * b == oa * ob + (if oa < ob then ob else oa);
    assert (if oa < ob then ob else oa) <= oa * ob;
    assert a * b <= 2 * (oa * ob);
    steps := steps + 2;
  }
  output := IntToString(a + b);
  steps := steps + 1;
}
