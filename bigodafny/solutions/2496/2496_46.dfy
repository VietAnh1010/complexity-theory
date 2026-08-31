// 442_B. Andrey and Problem  (problem 2496, solution 2496_46)
// time complexity: O(n**2)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import bisect
// n=int(input())
// ls=list(map(float,input().split()))
// ls.sort()
// mx=ls[-1]
// idx=bisect.bisect_left(ls,0.5)
// if idx<n and ls[idx]<0.5:
//     idx+=1
// 
// res=0
// st=0
// while(st<idx-1):
//     temp=0
//     for i in range(st,idx):
//         t=1
//         for j in range(st,idx):
//             if i!=j:
//                 t=t*(1-ls[j])
//                 
//         temp+=t*ls[i]
//     res=max(res,temp)
//     st+=1
// res=max(res,mx)
// print("%.12f"%res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<real>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
