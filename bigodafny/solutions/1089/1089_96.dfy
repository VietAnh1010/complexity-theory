// 124_A. The number of positions  (problem 1089, solution 1089_96)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, a, b = list(map(int, input().split()))
// ans = 0
// for i in range(n):
//     if i >= a and n - i - 1 <= b:
//         ans += 1
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
