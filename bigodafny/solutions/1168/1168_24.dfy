// 1322_A. Unusual Competitions  (problem 1168, solution 1168_24)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// input()
// s = input()
// t = 0
// l = 0
// e = -1
// for i in range(len(s)):
//     if s[i] == "(":
//         l += 1
//         if l == 0:
//             t += i-e+1
//     elif s[i] == ")":
//         l -= 1
//         if l == -1:
//             e = i
// if l != 0:
//     print(-1)
// else:
//     print(t)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  var t := 0;
  var l := 0;
  var e := -1;
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if s[i] == '(' {
      l := l + 1;
      if l == 0 {
        t := t + (i - e + 1);
      }
    } else if s[i] == ')' {
      l := l - 1;
      if l == -1 {
        e := i;
      }
    }
    i := i + 1;
  }
  if l != 0 {
    output := "-1";
  } else {
    output := IntToString(t);
  }
}
