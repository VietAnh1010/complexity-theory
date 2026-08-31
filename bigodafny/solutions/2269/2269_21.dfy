// 981_A. Antipalindrome  (problem 2269, solution 2269_21)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s, r = input(), 0
// i = len(s)
// while i > r:
//     for j in range(i - r):
//         t = s[j:i]
//         if t != t[::-1]:
//             r = i - j
//             break
//     i -= 1
// print(r)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
