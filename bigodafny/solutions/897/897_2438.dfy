// 617_A. Elephant  (problem 897, solution 897_2438)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x = int(input())
// step = 0
// while x != 0:
//     if x >= 5:
//         step += 1
//         x = x - 5
//     elif x >= 4:
//         step += 1
//         x = x - 4
//     elif x >= 3:
//         step += 1
//         x = x - 3
//     elif x >= 2:
//         step += 1
//         x = x - 2
//     elif x >= 1:
//         step += 1
//         x = x - 1
// print(int(step))
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(number: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
