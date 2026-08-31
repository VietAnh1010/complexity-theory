// 202_A. LLPS  (problem 3017, solution 3017_340)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// k=0
// t=0
// for i in range(len(s)):
//     if ord(s[i])>k:
//         k=ord(s[i])
//         t=s[i]
// print(str(t)*s.count(chr(k)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(string_: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
