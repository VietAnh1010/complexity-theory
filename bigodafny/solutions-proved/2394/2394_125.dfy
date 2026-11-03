// 1296_E1. String Coloring (easy version)  (problem 2394, solution 2394_125)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

include "../../prelude.dfy"

lemma Sq2394(n: nat, K: nat)
  requires K == 13 * n + 4
  ensures n * K == 13 * (n * n) + 4 * n
{
}

method Solve(n: int, string_: string)
    returns (output: string, ghost steps: nat)
  requires 1 <= n <= |string_|
  ensures steps <= 13 * (n * n) + 30 * n + 20 + |output|
{
  steps := 0;
  var dp: seq<int> := [];
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    invariant |dp| == t
    invariant steps <= 6 * t
    decreases n - t
  {
    steps := steps + 2;
    steps := steps + (1 + |[1]|);
    dp := dp + [1];
    steps := steps + 1;
    t := t + 1;
  }
  steps := steps + 1;
  ghost var K: nat := 13 * n + 4;
  ghost var B := steps;
  var i := 1;
  while i < n
    invariant 1 <= i
    invariant i <= n
    invariant |dp| == n
    invariant steps <= B + (i - 1) * K
    decreases n - i
  {
    steps := steps + 2;
    var j := 0;
    ghost var s0 := steps;
    while j < i
      invariant 0 <= j <= i
      invariant |dp| == n
      invariant steps <= s0 + 13 * j
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
    CostMulDistrib(i - 1, 1, i, K);
    i := i + 1;
  }
  assert (i - 1) * K <= n * K by { CostMulMonoLeft(i - 1, n, K); }
  Sq2394(n, K);
  steps := steps + 1;
  var fl := true;
  var k := 0;
  while k < n
    invariant 0 <= k
    invariant k <= n
    invariant |dp| == n
    invariant steps <= B + n * K + 5 * k + 1
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
    while m < n
      invariant 1 <= m
    invariant m <= n
      invariant |ans| == m
      invariant steps <= B + n * K + 5 * n + 4 + 7 * m
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
