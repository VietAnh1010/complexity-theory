// 667_B. Coat of Anticubism  (problem 2071, solution 2071_33)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// data = [int(i) for i in input().split()]
// mx, box = 0, 0
// for i in data:
//     if i > mx:
//         box += mx
//         mx = i
//     else:
//         box += i
// print(mx - box + 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
