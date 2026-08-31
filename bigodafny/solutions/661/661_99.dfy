// 1323_C. Unusual Competitions  (problem 661, solution 661_99)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// brak=[i for i in input()]
// open_=0
// close_=0
// if brak.count('(')!=brak.count(')'):
//     print(-1)
// else:
//     count=0
//     for i in brak:
//         if i=="(":
//             open_+=1
//         else:
//             close_+=1
//             if close_>open_:
//                count+=2
//     print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
