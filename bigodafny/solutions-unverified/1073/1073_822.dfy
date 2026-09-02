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

method Solve(n: int) returns (output: string)
{
  var rawN := n + 1;
  var fact := 1;
  var i := 2;
  while i < rawN
    decreases rawN - i
  {
    fact := fact * i;
    i := i + 1;
  }
  output := IntToString(FloorDiv(fact * 2, rawN));
}

