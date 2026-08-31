// 110_C. Lucky Sum of Digits  (problem 271, solution 271_51)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// x,y=n//7,n%7
// z,w=y//4,y%4
// if(x<w):
//     print(-1)
// else:
//     print('4'*(z+w*2)+'7'*(x-w))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
