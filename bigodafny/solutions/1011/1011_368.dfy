// 1099_B. Squares and Segments  (problem 1011, solution 1011_368)
// time complexity: O(sqrt(n))
// label corrected 2026-10-20: BigOBench says O(n); solutions-proved/1011/1011_368.dfy bounds steps by 12 * CSqrt(n)
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

method Solve(n: int) returns (output: string)
{
  var a := 1;
  var b := 1;
  while a * b < n
    decreases n - a * b
  {
    if a < b { a := a + 1; } else { b := b + 1; }
  }
  output := IntToString(a + b);
}
