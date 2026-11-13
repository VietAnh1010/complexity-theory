// 1433_E. Two Round Dances  (problem 1073, solution 1073_822)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// fact = 1
// n = int(input())
// for i in range(2, n):
//     fact *= i
// print(fact * 2 // n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 0
  ensures steps <= 3 * n + 8 + |output|
{
  steps := 1;
  var rawN := n + 1;
  steps := steps + 1;
  var fact := 1;
  var i := 2;
  while i < rawN
    invariant 2 <= i <= rawN || rawN < 2
    invariant rawN >= 1
    invariant rawN < 2 ==> i == 2
    invariant steps + 0 <= 1 + 3 * (if i > 2 then i - 2 else 0) + 1 && steps >= 1
    decreases rawN - i
  {
    fact := fact * i;
    i := i + 1;
    steps := steps + 3;
  }
  steps := steps + 2;
  output := IntToString(FloorDiv(fact * 2, rawN));
  IntToStringDigits(FloorDiv(fact * 2, rawN));
  steps := steps + Digits(FloorDiv(fact * 2, rawN));
}

