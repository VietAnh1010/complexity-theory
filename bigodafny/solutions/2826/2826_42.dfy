// 608_C. Chain Reaction  (problem 2826, solution 2826_42)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// lis=[0]*(1000004)
// dp=[0]*(1000004)
// for i in range(n):
//     a,b = map(int,input().split())
//     lis[a]=b
// if lis[0]>0:
//     dp[0]=1    
// for i in range(1,1000002):
//     if lis[i]>0:
//         dp[i]=dp[max(-1,i-lis[i]-1)]+1
//     else:
//         dp[i]=dp[i-1]        
// print(n-max(dp))        
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
