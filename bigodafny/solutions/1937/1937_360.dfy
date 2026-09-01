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

method Solve(a: int, b: int, c: int) returns (output: string)
{
  var bVal := a;
  var gVal := b;
  var nVal := c;
  var m := bVal + gVal - nVal;
  if bVal < m { m := bVal; }
  if gVal < m { m := gVal; }
  if nVal < m { m := nVal; }
  output := IntToString(1 + m);
}
