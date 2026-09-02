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
  var best := 0;
  var i := 0;
  while i < |values|
    decreases |values| - i
  {
    if FloorMod(m, values[i]) == 0 && values[i] > best {
      best := values[i];
    }
    i := i + 1;
  }
  output := IntToString(FloorDiv(m, best));
}
