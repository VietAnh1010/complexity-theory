// 1433_E. Two Round Dances  (problem 1073, solution 1073_645)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def f(a):
//   res = 1
//   for i in range(1, 1+a):
//     res *= i
//   return res
// n = int(input())
// print(f(n) * f(n//2 - 1) ** 2 // f(n//2) ** 2 // 2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var rawN := n + 1;
  var half := FloorDiv(rawN, 2);
  var numerator := Factorial(rawN) * Factorial(half - 1) * Factorial(half - 1);
  var denom := Factorial(half) * Factorial(half);
  var step := FloorDiv(numerator, denom);
  output := IntToString(FloorDiv(step, 2));
}


function Factorial(a: int): int
  decreases if a < 0 then 0 else a
{
  if a <= 0 then 1 else a * Factorial(a - 1)
}
