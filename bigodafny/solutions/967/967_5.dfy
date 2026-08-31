// 68_B. Energy exchange  (problem 967, solution 967_5)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int, input().split())
// a = sorted(list(map(int, input().split())))
//  
// left = 0
// right = a[-1]
// for i in range(100):
//     mid = (left + right) / 2.0
//  
//     s1 = sum([x - mid for x in a if x >= mid]) * (100 - k) / 100.0
//     s2 = sum([mid - x for x in a if x < mid])
//     
//     if s1 >= s2:
//         left = mid
//     else:
//         right = mid
//  
// print(left)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, limit: int, v: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
