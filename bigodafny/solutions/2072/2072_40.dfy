// 758_B. Blown Garland  (problem 2072, solution 2072_40)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// arr = input()
// n = len(arr)
// r, b, y, g = 0, 0, 0, 0
// 
// for i in range(4):
//     if i >= n:
//         break
//     ltrs = sorted(arr[i::4])
//     let = ltrs[len(ltrs) - 1]
//     a = ltrs.count('!')
//     if let == 'R':
//         r += a
//     elif let == 'B':
//         b += a
//     elif let == 'Y':
//         y += a
//     elif let == 'G':
//         g += a
// 
// print(r, b, y, g)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
