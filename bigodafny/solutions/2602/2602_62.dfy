// 1351_A. A+B (Trial Problem)  (problem 2602, solution 2602_62)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// for q in range(t):
// 	a, b = map(int, input().split())
// 	print(a + b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, pairs_list: seq<seq<int>>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < |pairs_list|
    decreases |pairs_list| - i
  {
    var p := pairs_list[i];
    var s := if |p| >= 2 then p[0] + p[1] else 0;
    parts := parts + [IntToString(s)];
    i := i + 1;
  }
  output := Join(parts, "\n") + "\n";
}
