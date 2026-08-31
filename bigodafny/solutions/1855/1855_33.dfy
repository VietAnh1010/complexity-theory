// 80_B. Depression  (problem 1855, solution 1855_33)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// import sys
// 
// hm=str(input())
// h=12-(int(hm[0]+hm[1])%12)
// m=int(hm[3]+hm[4])
// 
// 
// print(360-(30*h-m/2),end=" ")
// print((m*6)%360)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(hour: string, minute: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
