// 1043_C. Smallest Word  (problem 1913, solution 1913_104)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = input()
// ss = sorted(s)
// r = [0] * len(s)
// b_char = 'b'
// for i, c in enumerate(reversed(s)):
//     if c != b_char:
//         r[len(s)-i-1] = 1
//         b_char = 'a' if b_char == 'b' else 'b'
// print(" ".join([str(i) for i in r]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  var n := |s|;
  var r := seq(n, _ => 0);
  var bChar := 'b';
  var idx := n - 1;
  while idx >= 0
    decreases idx + 1
  {
    if s[idx] != bChar {
      r := r[idx := 1];
      bChar := if bChar == 'b' then 'a' else 'b';
    }
    idx := idx - 1;
  }
  output := JoinInts(r, " ");
}
