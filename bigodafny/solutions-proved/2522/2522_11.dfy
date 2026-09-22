// 171_B. Star  (problem 2522, solution 2522_11)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// sum = 1
// n = int(input())
// if n ==1:
//     print(sum)
// else:
//     for i in range(1, n):
//         sum += 12*i
//     print(sum)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 1
  ensures steps <= 4 * n + 4
{
  var total := 1;
  steps := 1;
  if n == 1 {
    output := IntToString(total);
    steps := steps + 1;
  } else {
    var i := 1;
    ghost var base1 := steps;
    while i < n
      invariant 1 <= i
      invariant n >= 1 ==> i <= n
      invariant steps == base1 + 4 * (i - 1)
      decreases n - i
    {
      total := total + 12 * i;
      i := i + 1;
      steps := steps + 4;
    }
    output := IntToString(total);
    steps := steps + 1;
  }
}
