// 355_A. Vasya and Digital Root  (problem 457, solution 457_27)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// k, d = map(int, input().split(' '))
// if d == 0:
//     if k == 1:
//         print(0)
//     else:
//         print('No solution')
// else:
//     print(d, end = '')
//     for i in range(k - 1):
//         print("0", end = '')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
