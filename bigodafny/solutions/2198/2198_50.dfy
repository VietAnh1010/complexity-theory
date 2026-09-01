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
  var d0 := 0;
  var d1 := AbsInt(a_list[1] - a_list[0]);
  var maxi := d1;
  var i := 1;
  while i < n - 1
    decreases n - 1 - i
  {
    var diff := AbsInt(a_list[i] - a_list[i+1]);
    var nd0 := if d1 - diff > 0 then d1 - diff else 0;
    var nd1 := if d0 + diff > 0 then d0 + diff else 0;
    if nd0 > maxi { maxi := nd0; }
    if nd1 > maxi { maxi := nd1; }
    d0 := nd0;
    d1 := nd1;
    i := i + 1;
  }
  output := IntToString(maxi);
}
