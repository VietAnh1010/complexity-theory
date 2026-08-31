// 579_A. Raising Bacteria  (problem 945, solution 945_880)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// is_debug = False
// 
// x = int(input())
// 
// print(f'{bin(x).count("1")}')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var m := n;
  var count := 0;
  while m > 0
    decreases m
  {
    count := count + m % 2;
    m := m / 2;
  }
  output := IntToString(count) + "\n";
}
