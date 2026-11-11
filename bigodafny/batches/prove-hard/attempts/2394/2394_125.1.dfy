// --- Python ---------------------------------------------------------
// #code
// n = int(input())
// s = input()
// fl = True
// dp = [1]*n
// for i in range(1,n):
//     for j in range(i):
//         if s[j] > s[i]:
//             dp[i] = max(dp[i],1+dp[j])
// for i in dp:
//     if i>=3:
//         fl = False
//         break
// if not fl:
//     print("NO")
// else:
//     ans = "0"
//     mx = s[0]
//     for i in range(1,n):
//         if s[i] >= mx:
//             ans += "0"
//             mx = s[i]
//         else:
//             ans += "1"
//     print("YES")
//     print(ans)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(n: int, string_: string)
    returns (output: string, ghost steps: nat)
  requires 1 <= n <= |string_|
  ensures steps <= n * (13 * n + 4) + 30 * n + 20
{
  steps := 0;
  var dp: seq<int> := [];
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    invariant |dp| == t
    invariant steps == 5 * t
    decreases n - t
  {
    steps := steps + 2;
    steps := steps + (1 + |[1]|);
    dp := dp + [1];
    steps := steps + 1;
    t := t + 1;
  }
  steps := steps + 1;
  ghost var base := steps;
  ghost var K := 13 * n + 4;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant steps <= base + (i - 1) * K
    invariant base == 5 * n + 1
    invariant K == 13 * n + 4
    invariant |dp| == n
    decreases n - i
  {
    steps := steps + 2;
    ghost var s0 := steps;
    var j := 0;
    while j < i
      invariant steps <= s0 + 13 * j
      invariant 0 <= j <= i
      invariant |dp| == n
      decreases i - j
    {
      steps := steps + 2;
      steps := steps + 3;
      if string_[j] > string_[i] {
        steps := steps + 4;
        if 1 + dp[j] > dp[i] {
          steps := steps + 3;
          dp := dp[i := 1 + dp[j]];
        }
      }
      steps := steps + 1;
      j := j + 1;
    }
    steps := steps + 1;
    steps := steps + 1;
    MulStep(i, K);
    i := i + 1;
  }
  steps := steps + 1;
  MulLe(i - 1, n, K);
  var fl := true;
  ghost var s2 := steps;
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant steps <= s2 + 5 * k
    invariant |dp| == n
    decreases n - k
  {
    steps := steps + 2;
    steps := steps + 2;
    if dp[k] >= 3 {
      fl := false;
    }
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 1;
  steps := steps + 1;
  if !fl {
    output := "NO";
  } else {
    var ans := "0";
    steps := steps + 1;
    var mx := string_[0];
    var m := 1;
    ghost var s3 := steps;
    while m < n
      invariant 1 <= m <= n
      invariant |ans| == m
      invariant steps <= s3 + 8 * (m - 1)
      decreases n - m
    {
      steps := steps + 2;
      steps := steps + 2;
      if string_[m] >= mx {
        steps := steps + |"0"|;
        ans := ans + "0";
        steps := steps + 1;
        mx := string_[m];
      } else {
        steps := steps + |"1"|;
        ans := ans + "1";
      }
      steps := steps + 1;
      m := m + 1;
    }
    steps := steps + 1;
    steps := steps + |ans|;
    output := "YES\n" + ans;
  }
}

import opened Prelude

lemma MulStep(i: int, K: int)
  ensures i * K == (i - 1) * K + K
{}

lemma MulLe(a: int, n: int, K: int)
  requires 0 <= a <= n && 0 <= K
  ensures a * K <= n * K
{}
