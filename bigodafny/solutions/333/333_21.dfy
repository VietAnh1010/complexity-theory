// 938_A. Word Correction  (problem 333, solution 333_21)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// k = input()
// s = input()
// vowels = ['a','e','i','o','u','y']
// new = []
// new.append(s[0])
// curr = s[0]
// for i in range(1, len(s)):
//     if curr in vowels and s[i] in vowels:
//         continue
//     else:
//         new.append(s[i])
//         curr = s[i]
// 
// print(''.join(new))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, word: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
