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
  var size := 1000004;
  var lis := new int[size];
  var dp := new int[size];
  var z := 0;
  while z < size
    invariant 0 <= z <= size
  {
    lis[z] := 0;
    dp[z] := 0;
    z := z + 1;
  }
  var idx := 0;
  while idx < |pairs|
    invariant 0 <= idx <= |pairs|
  {
    var row := pairs[idx];
    if |row| >= 2 {
      var a := row[0];
      var b := row[1];
      if 0 <= a < size {
        lis[a] := b;
      }
    }
    idx := idx + 1;
  }
  if lis[0] > 0 {
    dp[0] := 1;
  }
  var i := 1;
  while i < 1000002
    invariant 1 <= i <= 1000002
  {
    if lis[i] > 0 {
      var back := i - lis[i] - 1;
      if back >= 0 && back < i {
        dp[i] := dp[back] + 1;
      } else {
        dp[i] := 0 + 1;
      }
    } else {
      dp[i] := dp[i-1];
    }
    i := i + 1;
  }
  var best := 0;
  var k := 0;
  while k < size
    invariant 0 <= k <= size
  {
    if dp[k] > best { best := dp[k]; }
    k := k + 1;
  }
  output := IntToString(n - best);
}
