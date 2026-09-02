// 195_A. Let's Watch Football  (problem 1580, solution 1580_118)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a , b, c = list(map(int, input().split()))
// 
// 
// 
// 
// t = a*c
// 
// if t%b == 0:
//     print(t//b - c)
// else:
//     print(t//b -c +1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int) returns (output: string)
{
  var t := a * c;
  if FloorMod(t, b) == 0 {
    output := IntToString(FloorDiv(t, b) - c);
  } else {
    output := IntToString(FloorDiv(t, b) - c + 1);
  }
}
