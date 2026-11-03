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
import opened Prelude

lemma Sq2394(n: nat, K: nat)
  requires K == 10 * n + 4
  ensures n * K == 10 * (n * n) + 4 * n
{
}

method Solve(n: int, string_: string) returns (output: string, ghost steps: nat)
  requires 1 <= n <= |string_|
  ensures steps <= 10 * (n * n) + 20 * n + 20
{
  steps := 1;
  var dp: seq<int> := [];
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    invariant |dp| == t
    invariant steps == 1 + 3 * t
    decreases n - t
  {
    dp := dp + [1];
    t := t + 1;
    steps := steps + 3;
  }

  ghost var K: nat := 10 * n + 4;
  var i := 1;
  steps := steps + 1;
  while i < n
    invariant 1 <= i <= n
    invariant |dp| == n
    invariant steps <= 1 + 3 * n + 1 + (i - 1) * K
    decreases n - i
  {
    var j := 0;
    ghost var s0 := steps;
    while j < i
      invariant 0 <= j <= i
      invariant |dp| == n
      invariant steps <= s0 + 10 * j
      decreases i - j
    {
      if string_[j] > string_[i] {
        if 1 + dp[j] > dp[i] {
          dp := dp[i := 1 + dp[j]];
        }
      }
      j := j + 1;
      steps := steps + 10;
    }
    CostMulDistrib(i - 1, 1, i, K);
    i := i + 1;
    steps := steps + 4;
  }
  assert (i - 1) * K <= n * K by { CostMulMonoLeft(i - 1, n, K); }
  Sq2394(n, K);

  var fl := true;
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant |dp| == n
    invariant steps <= 1 + 3 * n + 1 + n * K + 5 * k
    decreases n - k
  {
    if dp[k] >= 3 {
      fl := false;
    }
    k := k + 1;
    steps := steps + 5;
  }

  if !fl {
    output := "NO";
    steps := steps + 1;
  } else {
    var ans := "0";
    var mx := string_[0];
    var m := 1;
    steps := steps + 3;
    while m < n
      invariant 1 <= m <= n
      invariant |ans| == m
      invariant steps <= 1 + 3 * n + 1 + n * K + 5 * n + 3 + 6 * (m - 1)
      decreases n - m
    {
      if string_[m] >= mx {
        ans := ans + "0";
        mx := string_[m];
      } else {
        ans := ans + "1";
      }
      m := m + 1;
      steps := steps + 6;
    }
    output := "YES\n" + ans;
    steps := steps + |ans|;
  }
}
