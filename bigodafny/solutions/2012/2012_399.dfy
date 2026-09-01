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

method Solve(n: int, k: int, pairs: seq<seq<int>>) returns (output: string)
{
  var mx := -1000000000;
  var i := 0;
  while i < n
    decreases n - i
  {
    var a := pairs[i][0];
    var b := pairs[i][1];
    var v := if a < a - (b - k) then a else a - (b - k);
    if v > mx {
      mx := v;
    }
    i := i + 1;
  }
  output := IntToString(mx);
}
