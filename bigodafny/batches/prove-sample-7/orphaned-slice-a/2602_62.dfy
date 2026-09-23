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

// Every part is IntToString(s): under the digit-string exception in
// COMPLEXITY.md, both IntToString(x) and |IntToString(x)| are charged 1, so
// Join over these k parts costs k rather than the sum of their true lengths.
method Solve(N: int, pairs_list: seq<seq<int>>) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * |pairs_list| + 3
{
  var parts: seq<string> := [];
  var i := 0;
  steps := 1;
  while i < |pairs_list|
    invariant 0 <= i <= |pairs_list|
    invariant |parts| == i
    invariant steps <= 1 + 3 * i
    decreases |pairs_list| - i
  {
    var p := pairs_list[i];
    var s := if |p| >= 2 then p[0] + p[1] else 0;
    parts := parts + [IntToString(s)];
    i := i + 1;
    steps := steps + 3;
  }
  output := Join(parts, "\n") + "\n";
  steps := steps + |parts| + 1;
}
