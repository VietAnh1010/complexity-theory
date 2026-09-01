// 1214_B. Badges  (problem 1937, solution 1937_10)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// b = int(input())
// g = int(input())
// n = int(input())
// bn = list(range(n+1))
// gn = list(reversed(list(range(n+1))))
// res = 0
// for i in range(n+1):
//     if bn[i] > b:
//         continue
//     if gn[i] > g:
//         continue
//     res += 1
// print(res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int) returns (output: string)
{
  var bLim := a;
  var gLim := b;
  var n := c;
  var res := 0;
  var i := 0;
  while i <= n
    decreases n - i
  {
    if i <= bLim && (n - i) <= gLim {
      res := res + 1;
    }
    i := i + 1;
  }
  output := IntToString(res);
}
