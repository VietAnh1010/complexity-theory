// 245_A. System Administrator  (problem 2719, solution 2719_289)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [0, 0]
// b = [0, 0]
// for i in range(n):
//     t, x, y = (int(x) for x in input().split())
//     if t == 1:
//         a[0] += x
//         a[1] += y
//     else:
//         b[0] += x
//         b[1] += y
// if a[0] >= a[1]:
//     print('LIVE')
// else:
//     print('DEAD')
// if b[0] >= b[1]:
//     print('LIVE')
// else:
//     print('DEAD')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values_list: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
