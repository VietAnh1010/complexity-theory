// 214_A. System of Equations  (problem 482, solution 482_438)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m = map(int, input().split())
// r=range(32)
// print(sum(a**2+b-n == b**2+a-m == 0 for a in r for b in r))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
