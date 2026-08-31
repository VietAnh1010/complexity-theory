// 112_A. Petya and Strings  (problem 3060, solution 3060_6262)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def sort(x, y):
//     a=sorted(x+y)
//     return a[-1]
// 
// n=input().lower()
// m=input().lower()
// 
// for i in range (0, len(n)):
//     if n[i]==m[i]:
//         if i==len(n)-1:
//             print(0)
//         continue
//     else:
//         if sort(n[i], m[i])==n[i]:
//             print(1)
//             break
//         else:
//             print(-1)
//             break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s1: string, s2: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
