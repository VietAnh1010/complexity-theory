// 1043_C. Smallest Word  (problem 1913, solution 1913_99)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = input()
// b = 1
// up = len(s)-1
// out = [0]*len(s)
// while up > -1:
//     if b == 1:
//         if s[up] == 'b':
//             out[up] = 0
//         else:
//             out[up] = 1
//             b = (b+1)%2
//     else:
//         if s[up] == 'a':
//             out[up] = 0
//         else:
//             out[up] = 1
//             b = (b+1)%2
//     up -= 1
// ans = ""
// for i in range(len(s)):
//     ans += str(out[i])+" "
// print(ans[:-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 7 * |s| + |output| + 4
{
  steps := 2;
  var n := |s|;
  var out := seq(n, _ => 0);
  steps := steps + n;
  var bChar := 'b';
  var idx := n - 1;
  while idx >= 0
    invariant -1 <= idx < n
    invariant |out| == n
    invariant steps == 2 + n + 7 * (n - 1 - idx)
    decreases idx + 1
  {
    if s[idx] != bChar {
      out := out[idx := 1];
      bChar := if bChar == 'b' then 'a' else 'b';
    }
    idx := idx - 1;
    steps := steps + 7;
  }
  output := JoinInts(out, " ");
  if n >= 1 {
    JoinIntsLen(out, " ");
    steps := steps + SumDigits(out) + |out|;
  }
}
