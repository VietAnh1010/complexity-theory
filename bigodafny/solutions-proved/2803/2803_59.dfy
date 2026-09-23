// 630_H. Benches  (problem 2803, solution 2803_59)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// fact = 120
// print(n * n * ((n - 1) ** 2) * ((n - 2) ** 2) * ((n - 3) ** 2) * ((n - 4) ** 2) // fact)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= 10
{
  steps := 1;
  var fact := 120;
  steps := steps + 1;
  var val := n * n * ((n - 1) * (n - 1)) * ((n - 2) * (n - 2)) * ((n - 3) * (n - 3)) * ((n - 4) * (n - 4));
  steps := steps + 1;
  var result := FloorDiv(val, fact);
  steps := steps + 1;
  output := IntToString(result);
  steps := steps + 1;
}
