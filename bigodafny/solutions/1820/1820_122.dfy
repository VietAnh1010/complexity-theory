// 1199_A. City Day  (problem 1820, solution 1820_122)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,x,y=map(int,input().split())
// a=list(map(int,input().split()))
// 
// ind=0
// 
// for i in range(len(a)):
//     
//     chx=1
//     chy=1
//     
//     for j in range(i-x,i):
//         if(j>=0):
//             if(a[i]>=a[j]):
//                 chx=0
//                 break
//         
//     for j in range(i+1,i+y+1):
//         if(j<n):
//             if(a[i]>=a[j]):
//                 chy=0
//                 break
//         
//     if(chx==1 and chy==1):
//         ind=i
//         break
// 
// print(ind+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
