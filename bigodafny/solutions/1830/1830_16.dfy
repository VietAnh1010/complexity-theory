// 834_B. The Festive Evening  (problem 1830, solution 1830_16)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=map(int,input().split())
// s=input()
// m=0
// a=[0]*30
// b=[0]*30
// for i in s:
//     q=ord(i)-65
//     a[q]+=1
// for i in s:
//     q=ord(i)-65
//     if a[q]>0:
//         if b[q]==0:
//             if k==0:
//                 m=1
//                 break
//             b[q]=1
//             k-=1
//         a[q]-=1
//         if a[q]==0:
//             k+=1
//             b[q]=1
// if m==0:
//     print("NO")
// else:
//     print("YES")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, string_: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
