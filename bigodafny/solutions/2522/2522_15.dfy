// 171_B. Star  (problem 2522, solution 2522_15)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = int(input())
// 
// if a == 1:
//     print(1)
// else:
//     print(12 * (a - 1) * a // 2 + 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  if n == 1 {
    output := "1";
  } else {
    var result := FloorDiv(12 * (n - 1) * n, 2) + 1;
    output := IntToString(result);
  }
}
