// p03281 AtCoder Beginner Contest 106 - 105  (problem 1254, solution 1254_182)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from bisect import bisect_right
// 
// n = int(input())
// 
// print(bisect_right([105, 135, 165, 189, 195], n))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var arr := [105, 135, 165, 189, 195];
  var cnt := 0;
  var i := 0;
  while i < |arr|
    decreases |arr| - i
  {
    if arr[i] <= n { cnt := cnt + 1; }
    i := i + 1;
  }
  output := IntToString(cnt);
}
