// 774_C. Maximum Number  (problem 2880, solution 2880_23)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// if n % 2 == 0:
//     print('1'*(n//2))
// else:
//     print('7'+'1'*((n-3)//2))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  if n % 2 == 0 {
    var raw := n / 2;
    var c := if raw < 0 then 0 else raw;
    output := Repeat("1", c);
  } else {
    var raw := (n - 3) / 2;
    var c := if raw < 0 then 0 else raw;
    output := "7" + Repeat("1", c);
  }
}
