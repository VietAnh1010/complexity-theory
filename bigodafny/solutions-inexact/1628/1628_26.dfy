// 560_D. Equivalent Strings  (problem 1628, solution 1628_26)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def sm(s):
//     if len(s) % 2 == 1:
//         return s
//     s1 = sm(s[:len(s) // 2])
//     s2 = sm(s[len(s) // 2:])
//     if s1 < s2:
//         return s1 + s2
//     else:
//         return s2 + s1
//     
// if sm(input()) == sm(input()):
//     print("YES")
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s1: string, s2: string) returns (output: string)
{
  var n1 := Norm1628a(s1);
  var n2 := Norm1628a(s2);
  if n1 == n2 {
    output := "YES";
  } else {
    output := "NO";
  }
}

function Norm1628a(s: string): string
  decreases |s|
{
  if |s| % 2 == 1 then s
  else
    var half := |s| / 2;
    var a := Norm1628a(s[..half]);
    var b := Norm1628a(s[half..]);
    if StringLess(a, b) then a + b else b + a
}
