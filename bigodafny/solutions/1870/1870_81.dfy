// 1285_D. Dr. Evil Underscores  (problem 1870, solution 1870_81)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// n=int(input())
// arr=list(map(int,input().split()))
// def solve(arr,bit):
//     if len(arr)==0 or bit <0:
//         return 0
//     l=[]
//     r=[]
//     for i in arr:
//         if (i>>bit)&1==0:
//             l.append(i)
//         else:
//             r.append(i)
// 
// 
//     if len(l)==0:
//         return solve(r,bit-1)
// 
//     if len(r)==0:
//         return solve(l,bit-1)
// 
//     return min(solve(r,bit-1),solve(l,bit-1))+(1<<bit)
// print(solve(arr,30))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
