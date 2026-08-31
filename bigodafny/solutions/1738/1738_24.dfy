// 764_A. Taymyr is calling you  (problem 1738, solution 1738_24)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// m = [int(n) for n in input().split()]
// count = 0
// for i in range(1,m[2]+1):
//     if i%m[0] == 0 and i%m[1] == 0:
//         count = count + 1
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
