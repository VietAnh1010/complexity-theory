// 596_A. Wilbur and Swimming Pool  (problem 966, solution 966_54)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from sys import stdin
// n=int(stdin.readline().strip())
// s=[]
// for i in range(n):
//     
//     a,b=map(int,stdin.readline().strip().split())
//     s.append([a,b])
// ans=-1
// for i in range(n):
//     for j in range(i+1,n):
//         if( s[i][0]!=s[j][0] and  s[i][1]!=s[j][1] ):
//             
//             ans=abs(s[i][0]-s[j][0] )*  abs(s[i][1]-s[j][1] )  
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function PL(v: seq<seq<string>>, k: nat): nat
  decreases k
{
  if k == 0 || k > |v| then 0
  else PL(v, k - 1) + (if |v[k-1]| >= 2 then |v[k-1][0]| + |v[k-1][1]| else 0)
}

method Solve(n: int, values: seq<seq<string>>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |values| == n
  requires forall k :: 0 <= k < n ==> |values[k]| >= 2
  ensures steps <= n * (12 * n + 8) + 8 * n + PL(values, n) + |output| + 10
{
  steps := 1;
  var xs: seq<int> := [];
  var ys: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |xs| == i
    invariant |ys| == i
    invariant steps <= 1 + 8 * i + PL(values, i)
    decreases n - i
  {
    xs := xs + [ParseInt(values[i][0])];
    ys := ys + [ParseInt(values[i][1])];
    i := i + 1;
    steps := steps + 8 + |values[i-1][0]| + |values[i-1][1]|;
  }
  var ans := -1;
  i := 0;
  ghost var K: nat := 12 * n + 8;
  ghost var s0 := steps;
  while i < n
    invariant 0 <= i <= n
    invariant |xs| == n
    invariant |ys| == n
    invariant steps <= s0 + i * K
    decreases n - i
  {
    var j := i + 1;
    ghost var s1 := steps;
    while j < n
      invariant i + 1 <= j <= n
      invariant steps <= s1 + 12 * (j - i - 1)
      decreases n - j
    {
      if xs[i] != xs[j] && ys[i] != ys[j] {
        ans := AbsInt(xs[i] - xs[j]) * AbsInt(ys[i] - ys[j]);
      }
      j := j + 1;
      steps := steps + 12;
    }
    i := i + 1;
    steps := steps + 8;
    CostMulDistrib(i - 1, 1, i, K);
  }
  output := IntToString(ans);
  IntToStringDigits(ans);
  steps := steps + Digits(ans);
}
