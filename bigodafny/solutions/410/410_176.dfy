// 725_A. Jumping Ball  (problem 410, solution 410_176)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, s = int(input()), input()
// if '<' not in s or '>' not in s:
//     print(n)
// else:
//     print(s.find('>') + (n - 1 - s.rfind('<')))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, arrows: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
