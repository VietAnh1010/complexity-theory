// 112_A. Petya and Strings  (problem 3060, solution 3060_1359)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a=input().lower()
// b=input().lower()
// c=0
// while True:
//  try:
//   if a[c]==b[c]:
//    c+=1
//   else:
//    if a[c]<b[c]:
//     print(-1)
//     break
//    else:
//     print(1)
//     break
//  except IndexError:
//   print(0)
//   break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s1: string, s2: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
