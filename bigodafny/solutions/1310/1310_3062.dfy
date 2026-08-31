// 116_A. Tram  (problem 1310, solution 1310_3062)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// x = list(map(int, input().split()))
// s = []
// for i in range(0,x[0]):
//     s.append(list(map(int, input().split())))
// q = 1
// p = 0
// q = 0
// for i in range(0,x[0]):
//     p = p - s[i][0] + s[i][1]
//     if p > q :
//         q = p
// print(q)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
