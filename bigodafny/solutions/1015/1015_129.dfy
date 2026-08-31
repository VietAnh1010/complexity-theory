// 1205_A. Almost Equal  (problem 1015, solution 1015_129)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// n*=n%2
// print('YNEOS'[n<1::2],*(i%n*2+i%2+1for i in range(2*n)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
