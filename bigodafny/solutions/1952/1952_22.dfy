// 877_B. Nikita and string  (problem 1952, solution 1952_22)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// x1=0
// x2=0
// x3=0
// for i in range (len(s)):
//     if s[i]=='a':
//         x3=max(x2, x3)+1
//         x1+=1
//     else:
//         x2=max(x1, x2)+1
// x4=max(x1, x2)
// x5=max(x3, x4)
// print(x5)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
