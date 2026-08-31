// 1008_B. Turn the Rectangles  (problem 396, solution 396_58)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import inf
// 
// n = int(input())
// 
// last = inf
// flag = True
// 
// for _ in range(n):
//     w, h = map(int, input().split(" "))
//     if h < w:
//         w, h = h, w
//     if h <= last:
//         last = h
//     elif w <= last:
//         last = w
//     else:
//         flag = False
//         break
// 
// if flag:
//     print("YES")
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, rectangles: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
