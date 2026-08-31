// 621_B. Wet Shark and Bishops  (problem 750, solution 750_51)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// 
// a = [0] * 2001
// b = [0] * 2001
// for i in range(n):
//     x, y = map(int, input().split())
//     a[x - y] += 1
//     b[x + y] += 1
// 
// ans = 0
// for i in range(2001):
//     ans += a[i] * (a[i] - 1) // 2
//     ans += b[i] * (b[i] - 1) // 2
// 
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, data_points: seq<(int, int)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
