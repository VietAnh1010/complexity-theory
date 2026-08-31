// 257_B. Playing Cubes  (problem 433, solution 433_16)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def t(b, pr):
//     i, p = 1, [0, 0]
//     while b[0] or b[1]:
//         if i == 0:
//             c = pr if b[pr] else 1 - pr
//         else:
//             c = 1 - pr if b[1 - pr] else pr
//         p[c != pr] += 1
//         b[c] -= 1
//         i, pr = 1 - i, c
//     return p
// 
// n, m = map(int, input().split())
// v1, v2 = t([n - 1, m], 0), t([n, m - 1], 1)
// print(' '.join(map(str, v1 if v1[0] >= v2[0] else v2)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
