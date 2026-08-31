// 257_B. Playing Cubes  (problem 433, solution 433_57)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// f=input().split()
// kras=int(f[0])
// sin=int(f[1])
// print(max(kras,sin)-1,min(kras,sin))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var mx := if a > b then a else b;
  var mn := if a < b then a else b;
  output := IntToString(mx - 1) + " " + IntToString(mn);
}
