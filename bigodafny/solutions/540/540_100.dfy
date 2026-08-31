// 638_A. Home Numbers  (problem 540, solution 540_100)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, a = map(int, input().split())
// print(a // 2 + 1 if a % 2 else (n - a + 2) // 2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int) returns (output: string)
{
  if k % 2 != 0 {
    output := IntToString(k / 2 + 1);
  } else {
    output := IntToString((n - k + 2) / 2);
  }
}
