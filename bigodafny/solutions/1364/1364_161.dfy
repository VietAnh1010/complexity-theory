// 611_B. New Year and Old Property  (problem 1364, solution 1364_161)
// time complexity: O(logn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// ans = 0
// a, b = map(int, input().split())
// l = 2
// pos = l-2
// ans = 0
// while True:
//     n = ((1 << l) - 1) - (1 << pos)
//     #print(l, pos, n)
//     if n > b:
//         break
//     if n >= a:
//         ans += 1
//     if pos > 0:
//         pos -= 1
//     else:
//         l += 1
//         pos = l-2
// print(ans)
//
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var l := 2;
  var pos := 0; // l - 2
  var powL := 4; // 2^l
  var powPos := 1; // 2^pos
  var ans := 0;
  var done := false;
  while !done
    decreases (if powL - 1 - powPos > b then 0 else b - (powL - 1 - powPos) + 1)
  {
    var n := powL - 1 - powPos;
    if n > b {
      done := true;
    } else {
      if n >= a {
        ans := ans + 1;
      }
      if pos > 0 {
        pos := pos - 1;
        powPos := powPos / 2;
      } else {
        l := l + 1;
        pos := l - 2;
        powPos := powL / 2;
        powL := powL * 2;
      }
    }
  }
  output := IntToString(ans);
}
