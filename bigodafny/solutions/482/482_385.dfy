// 214_A. System of Equations  (problem 482, solution 482_385)
// time complexity: O(n**2+m**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m = map(int, input().split())
// c = 0
// for a in range(0,max(n ,m) + 1):
//     for b in range(0, max(n, m) + 1):
//         if ((a **2) + b) == n and (a + (b ** 2)) == m:
//             c = c + 1
// print(c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
