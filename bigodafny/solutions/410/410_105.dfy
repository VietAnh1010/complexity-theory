// 725_A. Jumping Ball  (problem 410, solution 410_105)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = input()
// 
// begin = True
// counter = 0
// ans = 0
// 
// for i in range(n):
//     if begin and s[i] == "<":
//         ans += 1
//     elif s[i] == ">":
//         counter += 1
//         begin = False
//     else:
//         counter = 0
// print(ans + counter)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, arrows: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
