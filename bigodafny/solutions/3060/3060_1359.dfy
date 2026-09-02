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
  var a := s1;
  var b := s2;
  var c := 0;
  while true
    invariant 0 <= c
    decreases |a| - c
  {
    if c >= |a| || c >= |b| {
      output := "0";
      return;
    }
    var ca: char := if a[c] >= 'A' && a[c] <= 'Z' then ((a[c] as int) + 32) as char else a[c];
    var cb: char := if b[c] >= 'A' && b[c] <= 'Z' then ((b[c] as int) + 32) as char else b[c];
    if ca == cb {
      c := c + 1;
    } else if ca < cb {
      output := "-1";
      return;
    } else {
      output := "1";
      return;
    }
  }
}
