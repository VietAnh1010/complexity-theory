// p03388 AtCoder Beginner Contest 093 - Worst Case  (problem 810, solution 810_98)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// q=int(input())
// def check(t,a,b):
//     k=(2*a+t)//2
//     return k*(2*a+t-k)<a*b
// 
// for i in range(q):
//     a,b=sorted(map(int,input().split()))
//     if a==b or a==b-1:
//         print(2*a-2)
//         continue
//     l,r=1,b-a
//     while l+1<r:
//         t=(l+r)//2
//         if check(t,a,b):
//             l=t
//         else:
//             r=t
//     
//     if check(r,a,b):
//         print(2*a-2+r)
//     elif check(l,a,b):
//         print(2*a-2+l)
//     else:
//         print(2*a-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
