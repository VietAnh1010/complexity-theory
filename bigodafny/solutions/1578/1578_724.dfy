// 1236_A. Stones  (problem 1578, solution 1578_724)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for i in range(int(input())):
//     a, b, c = map(int, input().split())
//     res = 0
//     while True:
//         if b >= 1 and c >= 2:
//             res += 3
//             c -= 2
//             b -= 1
//         elif a >= 1 and b >= 2:
//             res += 3
//             a -= 1
//             b -= 2
//         else:
//             print(res)
//             break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
