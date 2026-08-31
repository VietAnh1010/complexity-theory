// 416_A. Guess a number!  (problem 1878, solution 1878_29)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// u, v = -2000000000, 2000000000
// for i in range(int(input())):
//     a, b, c = input().split()
//     k = int(b)
//     if a == '>=':
//         if c == 'Y': u = max(u, k)
//         else: v = min(v, k - 1)
//     elif a == '>':
//         if c == 'Y': u = max(u, k + 1)
//         else: v = min(v, k)
//     elif a == '<=':
//         if c == 'Y': v = min(v, k)
//         else: u = max(u, k + 1)
//     else:
//         if c == 'Y': v = min(v, k - 1)
//         else: u = max(u, k)
// print('Impossible' if u > v else u)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, queries: seq<(string, int, string)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
