// 214_A. System of Equations  (problem 482, solution 482_438)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m = map(int, input().split())
// r=range(32)
// print(sum(a**2+b-n == b**2+a-m == 0 for a in r for b in r))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var n := a;
  var m := b;
  var c := 0;
  var av := 0;
  while av < 32
    decreases 32 - av
  {
    var bv := 0;
    while bv < 32
      decreases 32 - bv
    {
      if av * av + bv == n && bv * bv + av == m {
        c := c + 1;
      }
      bv := bv + 1;
    }
    av := av + 1;
  }
  output := IntToString(c);
}
