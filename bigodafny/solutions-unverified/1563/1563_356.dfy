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
  // m % v and the final m // best are what Python does; both raise
  // ZeroDivisionError without these, so the clauses exclude nothing Python
  // computes an answer for.
  requires forall k :: 0 <= k < |values| ==> values[k] != 0
  requires exists k :: 0 <= k < |values| && FloorMod(m, values[k]) == 0 && values[k] > 0
{
  var best := 0;
  var i := 0;
  while i < |values|
    invariant 0 <= i <= |values|
    invariant best >= 0
    invariant (exists k :: 0 <= k < i && FloorMod(m, values[k]) == 0 && values[k] > 0) ==> best > 0
    decreases |values| - i
  {
    if FloorMod(m, values[i]) == 0 && values[i] > best {
      best := values[i];
    }
    i := i + 1;
  }
  assert best > 0;
  output := IntToString(FloorDiv(m, best));
}
