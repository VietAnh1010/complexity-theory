// 788_A. Functions again  (problem 2198, solution 2198_50)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// dp=[[0,0] for i in range(n)]
// dp[0][1]=abs(a[1]-a[0])
// maxi=abs(a[1]-a[0])
// for i in range(1,n-1):
//     dp[i][0]=max(0,dp[i-1][1]-abs(a[i]-a[i+1]))
//     dp[i][1]=max(0,dp[i-1][0]+abs(a[i]-a[i+1]))
//     maxi=max(maxi,dp[i][0],dp[i][1])
// print(maxi)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
