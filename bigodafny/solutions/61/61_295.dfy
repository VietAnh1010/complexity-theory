// 1042_A. Benches  (problem 61, solution 61_295)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// m = int(input())
// l = []
// for i in range(n):
//   l.append(int(input()))
// 
// mz = max(l)
// 
// mx = mz + m
// s1 = sum(l) 
// s2 = s1 + m
// 
// x = s2 // n
// y = s2 % n
// 
// if y == 0:
//   if mz < x:
//     mn = x
//   else:
//     mn = mz
// elif y <=n:
//   if mz <= x:
//     mn = x + 1
//   else:
//     mn = mz
// 
// else:
//   z1 = y // n
//   z2 = y % n
//   if mz < x:
//     mn = x + z1
//   else:
//     mn = mz
// 
// print(mn, mx)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, ignored_lines: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
