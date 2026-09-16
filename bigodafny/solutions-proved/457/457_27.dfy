// 355_A. Vasya and Digital Root  (problem 457, solution 457_27)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// k, d = map(int, input().split(' '))
// if d == 0:
//     if k == 1:
//         print(0)
//     else:
//         print('No solution')
// else:
//     print(d, end = '')
//     for i in range(k - 1):
//         print("0", end = '')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int) returns (output: string, ghost steps: nat)
  ensures n >= 1 ==> steps <= 4 * n + 6
  ensures n < 1 ==> steps <= 6
{
  steps := 1;
  if m == 0 {
    if n == 1 {
      output := "0";
    } else {
      output := "No solution";
    }
    steps := steps + 1;
  } else {
    var s := IntToString(m);
    steps := steps + 1;
    var i := 0;
    // No `requires n >= 1` is added (the original signature has none), so the
    // invariant must stay valid for every n, including n <= 1 where the loop
    // guard is false from the start.
    while i < n - 1
      invariant 0 <= i
      invariant i <= (if n >= 1 then n - 1 else 0)
      invariant steps == 3 * i + 2
      decreases n - 1 - i
    {
      s := s + "0";
      i := i + 1;
      steps := steps + 3;
    }
    output := s;
    steps := steps + 1;
  }
}
