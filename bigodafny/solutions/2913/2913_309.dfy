// 1088_A. Ehab and another construction problem  (problem 2913, solution 2913_309)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// flag=0
// for i in range(1,t+1):
//     if flag!=1:
//         for j in range(1,t+1):
//             if flag!=1:
//                 if i%j == 0:
//                     if i*j>t:
//                         if i%j < t:
//                             a,b = i,j
//                             flag=1
// if flag==1:
//     print(a,b)
// else:
//     print("-1")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
