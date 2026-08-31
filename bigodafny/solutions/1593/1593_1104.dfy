// 977_B. Two-gram  (problem 1593, solution 1593_1104)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = input()
// if n == 2:
//     print(s)
// else:
//     m = 0
//     k = ''
//     t = set()
//     for i in range(n-1):
//         s1 = 0
//         if s[i:i+2] not in t:
//             t.add(s[i:i+2])
//             for j in range(n-1):
//                 if s[j:j+2] == s[i:i+2]:
//                     s1 += 1
//             if s1 > m:
//                 m = s1
//                 k = s[i:i+2]
//         else:
//             continue
//     print(k)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
