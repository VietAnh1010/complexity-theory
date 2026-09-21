// 1088_A. Ehab and another construction problem  (problem 2913, solution 2913_633)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x=int(input()); print(-1) if x==1 else print(x-(x%2),2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= 10
{
  steps := 1;
  if n == 1 {
    output := "-1\n";
    steps := steps + 1;
  } else {
    output := IntToString(n - n % 2) + " " + IntToString(2) + "\n";
    steps := steps + 5;
  }
}
