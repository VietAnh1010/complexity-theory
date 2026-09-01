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
  var x1 := 0;
  var x2 := 0;
  var x3 := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if s[i] == 'a' {
      x3 := (if x2 > x3 then x2 else x3) + 1;
      x1 := x1 + 1;
    } else {
      x2 := (if x1 > x2 then x1 else x2) + 1;
    }
    i := i + 1;
  }
  var x4 := if x1 > x2 then x1 else x2;
  var x5 := if x3 > x4 then x3 else x4;
  output := IntToString(x5);
}
