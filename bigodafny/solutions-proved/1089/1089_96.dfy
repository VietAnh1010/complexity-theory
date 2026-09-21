// 124_A. The number of positions  (problem 1089, solution 1089_96)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, a, b = list(map(int, input().split()))
// ans = 0
// for i in range(n):
//     if i >= a and n - i - 1 <= b:
//         ans += 1
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a: int, b: int) returns (output: string, ghost steps: nat)
  requires n >= 0
  ensures steps <= 4 * n + 4
{
  var ans := 0;
  var i := 0;
  steps := 1;
  while i < n
    invariant 0 <= i <= n
    invariant steps == 4 * i + 1
    decreases n - i
  {
    if i >= a && n - i - 1 <= b { ans := ans + 1; }
    i := i + 1;
    steps := steps + 4;
  }
  output := IntToString(ans);
  steps := steps + 1;
}
