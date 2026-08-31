// 915_A. Garden  (problem 1563, solution 1563_356)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k =map(int, input().split())
// a = list(map(int, input().split()))
// m = 0
// for i in a:
//     if k % i == 0:
//         m = max(m, i)
// print(k//m)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, values: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
