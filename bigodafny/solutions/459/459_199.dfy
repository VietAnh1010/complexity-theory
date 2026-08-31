// 519_C. A and B and Team Training  (problem 459, solution 459_199)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def training(n,m):
//     t=0
//     for i in range(5*(10**5)):
//         if n>=m and n>1 and m>0:
//             n-=2
//             m-=1
//             t+=1
//         elif n<m and n>0 and m>1:
//             n-=1
//             m-=2
//             t+=1
//         else:
//             return t
// 
// 
// 
// a,b=list(map(int,input().split(" ")))
// print(training(a,b))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
