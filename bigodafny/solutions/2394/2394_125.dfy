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

method Solve(n: int, string_: string) returns (output: string)
{
  var dp: seq<int> := [];
  var t := 0;
  while t < n
    decreases n - t
  {
    dp := dp + [1];
    t := t + 1;
  }

  var i := 1;
  while i < n
    decreases n - i
  {
    var j := 0;
    while j < i
      decreases i - j
    {
      if string_[j] > string_[i] {
        if 1 + dp[j] > dp[i] {
          dp := dp[i := 1 + dp[j]];
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }

  var fl := true;
  var k := 0;
  while k < n
    decreases n - k
  {
    if dp[k] >= 3 {
      fl := false;
    }
    k := k + 1;
  }

  if !fl {
    output := "NO";
  } else {
    var ans := "0";
    var mx := string_[0];
    var m := 1;
    while m < n
      decreases n - m
    {
      if string_[m] >= mx {
        ans := ans + "0";
        mx := string_[m];
      } else {
        ans := ans + "1";
      }
      m := m + 1;
    }
    output := "YES\n" + ans;
  }
}
