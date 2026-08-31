// p03281 AtCoder Beginner Contest 106 - 105  (problem 1254, solution 1254_187)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// x=0
// for i in range(1,n+1,2):
//     c=0
//     for j in range(1,i+1):
//         if i%j==0:
//             c+=1
//     if c==8:
//         x+=1
// print(x)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
