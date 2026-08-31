// 554_A. Kyoya and Photobooks  (problem 208, solution 208_189)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = input()
// d = set()
// for i in range(len(s)):
//     for a in range(26):
//         c = chr(ord('a') + a)
//         d.add(s[:i] + c + s[i:])
// for a in range(26):
//         c = chr(ord('a') + a)
//         d.add(s + c)
// print(len(d))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
