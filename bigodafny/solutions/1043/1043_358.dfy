// 1326_A. Bad Ugly Numbers  (problem 1043, solution 1043_358)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// for _ in range(n):
//     v = int(input())
//     if v == 1:
//         print(-1)
//     else:
//         print("2" + "3" * (v - 1))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
