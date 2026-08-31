// 617_A. Elephant  (problem 897, solution 897_1880)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x = int(input())
// ans = x // 5
// x %= 5
// if (x != 0):
//     ans += 1
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(number: int) returns (output: string)
{
  var ans := number / 5;
  var r := number % 5;
  if r != 0 { ans := ans + 1; }
  output := IntToString(ans) + "\n";
}
