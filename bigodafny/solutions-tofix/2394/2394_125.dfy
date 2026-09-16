// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-18
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     Inside the nested i/j double loop the Dafny does dp := dp[i := 1 +
//     dp[j]], a seq update costing O(n) per occurrence; for a descending
//     string this fires on all O(n**2) (i,j) pairs, giving O(n**3) total,
//     while Python's dp[i]=max(dp[i],1+dp[j]) is O(1) per write and
//     genuinely O(n**2).
//
//   how this label could be wrong, and what to check:
//     The label assumes dp[i] updates are O(1) as in Python's
//     dp[i]=max(...). Open the inner j-loop and confirm it does `dp :=
//     dp[i := 1 + dp[j]]`, a full seq copy costing O(n); with a strictly
//     decreasing string this update fires on every (i,j) pair inside the
//     O(n**2) double loop, so the real cost is O(n**3).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 69, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 2, "loops": 5,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": true, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

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
  requires 1 <= n <= |string_|
{
  var dp: seq<int> := [];
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    invariant |dp| == t
    decreases n - t
  {
    dp := dp + [1];
    t := t + 1;
  }

  var i := 1;
  while i < n
    invariant 1 <= i
    invariant |dp| == n
    decreases n - i
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant |dp| == n
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
    invariant 0 <= k
    invariant |dp| == n
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
      invariant 1 <= m
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
