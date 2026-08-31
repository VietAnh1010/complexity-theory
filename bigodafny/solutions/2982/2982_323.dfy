// 1102_C. Doors Breaking and Repairing  (problem 2982, solution 2982_323)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import ceil
// n, x, y = map(int, input().split())
// li = list(map(int, input().split()))
// if x > y:
//     print(len(li))
// else:
//     num = 0
//     for i in li:
//         if i <= x:
//             num += 1
//     print(ceil(num / 2))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
