// 579_A. Raising Bacteria  (problem 945, solution 945_255)
// time complexity: O(logn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// bacteria = 0
// while True:
//     if n == 1:
//         bacteria += 1
//         break
//     else:
//         bacteria += n%2
//         n = n//2
//     
// print(bacteria)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
  requires n >= 1
{
  var m := n;
  var bacteria := 0;
  var done := false;
  while !done
    invariant m >= 0
    invariant !done ==> m >= 1
    decreases m
  {
    if m == 1 {
      bacteria := bacteria + 1;
      done := true;
      m := 0;
    } else {
      bacteria := bacteria + m % 2;
      m := m / 2;
    }
  }
  output := IntToString(bacteria) + "\n";
}
