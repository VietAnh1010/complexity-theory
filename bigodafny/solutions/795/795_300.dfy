// 1430_A. Number of Apartments  (problem 795, solution 795_300)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// while(t>0):
//     n=int(input())
//     f=0
//     for i in range(n//3+1):
//         if(f==1):
//             break
//         for j in range(n//5+1):
//             if(f==1):
//                 break
//             for k in range(n//7+1):
//                 if(f==1):
//                     break
//                 if(3*i+5*j+7*k==n):
//                     print(i,j,k)
//                     f=1
//                     
//                     
//     if(f==0):
//         print(-1)
//     t=t-1
//         
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
