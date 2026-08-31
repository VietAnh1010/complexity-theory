// 489_C. Given Length and Sum of Digits...  (problem 2282, solution 2282_1118)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// m,s=map(int,input().split())
//  
// def ismax(m,s):
//     op1=str()
//     if s==0:
//         return(-1)
//     elif s>m*9:
//         return(-1)
//     else:
//         for i in range(m):
//             if s>9:
//                 op1=op1+'9'
//                 s-=9
//             elif 0<s<=9:
//                 op1=op1+str(s)
//                 s=0
//             else:
//                 op1=op1+'0'
//         return(int(op1))
// 
// def ismin(m,s):
//     op2=str()
//     lis=[]
//     if s==0:
//         return(-1)
//     elif s>m*9:
//         return(-1)
//     else:
//         l=max(1,s-9*(m-1))
//         op2=op2+str(l)
//         s=s-l
//         for i in range(m-1):
//             if s>9:
//                 lis.append(9)
//                 s-=9
//             elif 0<s<=9:
//                 lis.append(s)
//                 s=0
//             else:
//                 lis.append(0)
//         lis=sorted(lis)
//         if len(lis)==1:
//             op2=op2+str(*lis)
//         elif len(lis)>1:
//             st="".join(map(str,lis))
//             op2=op2+st
//         return(int(op2))
// if m==1 and s==0:
//     print(0, 0)
// else:
//     print(ismin(m,s),ismax(m,s))
//     
//                 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
