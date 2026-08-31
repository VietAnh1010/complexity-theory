// 981_A. Antipalindrome  (problem 2269, solution 2269_59)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// s = input()
// 
// def isPalindrome(s):
//     l = len(s)
//     for i in range(l // 2):
//         if s[i] != s[l - i - 1]:
//             return False
//     return True
// 
// if not isPalindrome(s):
//     print(len(s))
// elif all([c == s[0] for c in s]):
//     print(0)
// else:
//     print(len(s) - 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
