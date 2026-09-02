// p03346 AtCoder Grand Contest 024 - Backfront  (problem 785, solution 785_75)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N = int(input())
// P = [int(input()) for i in range(N)]
// 
// 
// Q = sorted([(p, i) for i, p in enumerate(P, start=1)])
// Q = [i for p, i in Q]
// 
// dp = [1] * (N + 1)
// for i in range(1, N):
//     if Q[i] > Q[i - 1]:
//         dp[i] = dp[i - 1] + 1
// 
// print(N - max(dp))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
  requires n >= 1
  requires |numbers| == n
{
  var pairs := seq(|numbers|, i requires 0 <= i < |numbers| => (numbers[i], i+1));
  var srt := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  var q := seq(|srt|, i requires 0 <= i < |srt| => srt[i].1);
  assert |q| == n;
  var dp := new int[n+1];
  var k := 0;
  while k <= n
    invariant 0 <= k <= n + 1
    decreases n - k
  {
    dp[k] := 1;
    k := k + 1;
  }
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    decreases n - i
  {
    if q[i] > q[i-1] {
      dp[i] := dp[i-1] + 1;
    }
    i := i + 1;
  }
  var mx := dp[0];
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    decreases n - i
  {
    if dp[i] > mx { mx := dp[i]; }
    i := i + 1;
  }
  output := IntToString(n - mx);
}
