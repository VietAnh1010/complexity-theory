// 385_B. Bear and Strings  (problem 1511, solution 1511_9)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// if len(s) < 4: print(0)
// else:
//     a=0
//     for i in range(len(s)):
//         d=s.find("bear", i)
//         if d>=0: a+=len(s)-d-3
//     print(a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(string_: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
