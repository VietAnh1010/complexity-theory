// p03362 AtCoder Beginner Contest 096 - Five  Five Everywhere  (problem 1303, solution 1303_8)
// time complexity: O(n**2)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// P, A = [2], [2]
// for i in range(3, 55556, 2):
//     for p in P:
//         if i % p == 0: break
//     else:
//         P.append(i)
//         if i % 5 == 2: A.append(i)
//     if len(A) == n: break
// print(*A)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
