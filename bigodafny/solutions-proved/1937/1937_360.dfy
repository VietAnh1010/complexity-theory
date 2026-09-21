// 1214_B. Badges  (problem 1937, solution 1937_360)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// b, g, n = (int(input()) for _ in range(3))
//
// print(1 + min(b+g-n, b, g, n))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int) returns (output: string, ghost steps: nat)
  ensures steps <= 8
{
  var bVal := a;
  var gVal := b;
  var nVal := c;
  var m := bVal + gVal - nVal;
  steps := 2;
  if bVal < m { m := bVal; }
  steps := steps + 1;
  if gVal < m { m := gVal; }
  steps := steps + 1;
  if nVal < m { m := nVal; }
  steps := steps + 1;
  output := IntToString(1 + m);
  steps := steps + 2;
}
