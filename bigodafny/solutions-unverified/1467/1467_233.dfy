// 672_A. Summer Camp  (problem 1467, solution 1467_233)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// t=''
// for i in range(n+100):
//     t+=str(i)
// print(t[n])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < N + 100
    decreases N + 100 - i
  {
    parts := parts + [IntToString(i)];
    i := i + 1;
  }
  var t := Join(parts, "");
  output := [t[N]];
}
