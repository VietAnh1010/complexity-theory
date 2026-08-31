// 489_C. Given Length and Sum of Digits...  (problem 2282, solution 2282_16)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=input().split()
// n[0]=int(n[0])
// n[1]=int(n[1])
// if n[1]==0:
//     if n[0]==1:
//         print('0 0')
//     if n[0]!=1:
//         print('-1 -1')
// elif n[0]*9<n[1]:
//     print('-1 -1')
// else:
//     i=(n[1]-1)//9
//     q=(n[1]-1)%9
//     mi=10**(n[0]-1)+q*10**i
//     while i>0:
//         mi+=9*10**(i-1)
//         i=i-1
//     ii=n[1]//9
//     qq=n[1]%9
//     if qq==0:
//         ma=ii*'9'+(n[0]-ii)*'0'
//     else:
//         ma=ii*'9'+str(qq)+'0'*(n[0]-ii-1)
//     print(mi,ma)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
