// 630_F. Selection of Personnel  (problem 2286, solution 2286_14)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// numinator = lambda x: n if x == 0 else (n - x)*numinator(x - 1)
// numinator5 = numinator(4)
// print(numinator5//120 + numinator5*(n - 5)//720 + numinator5*(n - 5)*(n - 6)//5040)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var numinator5 := n * (n - 1) * (n - 2) * (n - 3) * (n - 4);
  var result := numinator5 / 120 + numinator5 * (n - 5) / 720
    + numinator5 * (n - 5) * (n - 6) / 5040;
  output := IntToString(result);
}
