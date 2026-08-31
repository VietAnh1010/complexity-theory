// 1358_D. The Best Vacation  (problem 888, solution 888_179)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def sumprog(a, b):
//     return (a + b) * (b - a + 1) // 2
//  
//  
// n, x = map(int, input().split())
// d = list(map(int, input().split())) * 2
// max_hugs = 0
// i = 0
// j = 0
// days = 0
// hugs = 0
// while i < n:
//     if days + d[j] <= x:
//         days += d[j]
//         hugs += sumprog(1, d[j])
//         j += 1
//     else:
//         max_hugs = max(max_hugs, hugs + sumprog(d[j] - (x - days) + 1, d[j]))
//         hugs -= sumprog(1, d[i])
//         days -= d[i]
//         i += 1
// print(max_hugs)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
