// 1177_A. Digits Sequence (Easy Edition)  (problem 1501, solution 1501_177)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// print(''.join(str(x) for x in range(1, 2778))[int(input()) -1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var parts: seq<string> := [];
  var x := 1;
  while x < 2778
    invariant 1 <= x <= 2778
    decreases 2778 - x
  {
    parts := parts + [IntToString(x)];
    x := x + 1;
  }
  var s := Join(parts, "");
  output := [s[n - 1]] + "\n";
}
