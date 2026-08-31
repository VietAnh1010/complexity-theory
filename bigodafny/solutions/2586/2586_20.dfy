// 546_B. Soldier and Badges  (problem 2586, solution 2586_20)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l1=list(map(int,input().split()))
// l2=[0]*int(n*(n+1)/2)
// cost=0
// for i in range (n):
//     if(l2[l1[i]-1]==0):
//         l2[l1[i]-1]=1
//     elif(l2[l1[i]-1]==1):
//         while(l2[l1[i]-1]==1):
//             cost+=1
//             l1[i]+=1
//         l2[l1[i]-1]=1
// print(cost)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
