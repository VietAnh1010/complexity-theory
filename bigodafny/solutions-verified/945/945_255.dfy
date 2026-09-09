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

// Label O(logn) -- agrees, and this is the first logarithmic bound proved for a
// row that does not sort. `solutions-nlogn/` needed a CEILING log because a
// merge split of size k recurses on ceil(k/2); here the loop divides by two and
// rounds DOWN, so the matching function is a floor log and the step
//     m >= 2  ==>  Log2(m / 2) == Log2(m) - 1
// holds by definition. Matching the log's rounding to the code's rounding is
// what makes the induction close in one line instead of needing a lemma.
ghost function Log2(x: nat): nat
  decreases x
{
  if x <= 1 then 0 else 1 + Log2(x / 2)
}

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 1
  ensures steps <= 4 * Log2(n) + 8
{
  steps := 1;
  var m := n;
  var bacteria := 0;
  var done := false;
  while !done
    invariant m >= 0
    invariant !done ==> m >= 1
    invariant !done ==> steps == 4 * (Log2(n) - Log2(m)) + 1
    invariant done ==> steps <= 4 * Log2(n) + 5
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
    steps := steps + 4;
  }
  output := IntToString(bacteria) + "\n";
  steps := steps + 3;
}
