// 1425_H. Huge Boxes of Animal Toys  (problem 1170, solution 1170_10)
// time complexity: O(n*m)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for _ in range(t):
//     l=list(map(int,input().split()))
//     a=[0]*4
//     if(l[0]+l[3]!=0):
//         a[0]=1
//         a[3]=1
//     if(l[1]+l[2]!=0):
//         a[1]=1
//         a[2]=1
//     if((l[1]+l[0])%2==0):
//         a[0]=0
//         a[1]=0
//     else:
//         a[2]=0
//         a[3]=0
//     for x in a:
//         if(x==0):
//             print("Tidak",end=" ")
//         else:
//             print("Ya",end=" ")
//     print(" ")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrices: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
