// 276_A. Lunch Rush  (problem 2012, solution 2012_399)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// X = list(map(int, input().split()))
// MAX = -10**9
// for i in range(X[0]):
//     Y = list(map(int, input().split()))
//     MAX = max(MAX, min(Y[0], Y[0] - (Y[1] - X[1])))
// print(MAX)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(n*m). The row's own precondition says |pairs[idx]| == 2, and the body
// reads both positions and nothing else. There is no second dimension. Honest
// bound O(n) -- the seventh O(n*m) row in this directory to fail the same way.
method Solve(n: int, k: int, pairs: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n <= |pairs|
  requires forall idx :: 0 <= idx < |pairs| ==> |pairs[idx]| == 2
  ensures steps <= 8 * (if n > 0 then n else 0) + 4
{
  steps := 2;
  var mx := -1000000000;
  var i := 0;
  while i < n
    invariant 0 <= i
    invariant i > 0 ==> i <= n
    invariant steps == 8 * i + 2
    decreases n - i
  {
    var a := pairs[i][0];
    var b := pairs[i][1];
    var v := if a < a - (b - k) then a else a - (b - k);
    if v > mx {
      mx := v;
    }
    i := i + 1;
    steps := steps + 8;
  }
  output := IntToString(mx);
  steps := steps + 2;
}
