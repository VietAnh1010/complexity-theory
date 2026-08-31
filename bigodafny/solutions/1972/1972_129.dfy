// 614_A. Link/Cut Tree  (problem 1972, solution 1972_129)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// l,r,k = map(int,input().split())
// li = [k**i for i in range(100) if k**i >= l and k**i <= r]
// if len(li) == 0:
//     print(-1)
// else:
//     print(' '.join([str(s) for s in li]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
