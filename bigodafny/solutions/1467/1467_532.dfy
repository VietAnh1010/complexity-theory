// 672_A. Summer Camp  (problem 1467, solution 1467_532)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// if n <= 9:
//     print(n)
// elif n <= 189:
//     num = (n - 10) / 2 + 10
//     mod = (n - 10) % 2
//     s = str(num)
//     print(s[mod])
// else:
//     num = (n - 10 - 90 * 2) / 3 + 100
//     mod = (n - 10 - 90 * 2) % 3
//     s = str(num)
//     print(s[mod])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
