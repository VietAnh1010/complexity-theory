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

// Charge table: each int multiplication/comparison is 1, regardless of the
// magnitude of the operands. Factorial(a) recurses a times, so under the
// stipulated cost model calling it costs O(a), and the whole method is O(n).
// The label O(n**2) comes from profiling CPython, where Factorial(n) is an
// n-digit bignum and each multiplication in the recursion costs O(digits),
// making the *true* cost O(n**2). That gap is the cost model, not the proof:
// relation = tighter-costmodel.
ghost function FactorialSteps(a: int): nat
  decreases if a < 0 then 0 else a + 1
{
  if a <= 0 then 1 else 1 + FactorialSteps(a - 1)
}

lemma FactorialStepsBound(a: int)
  ensures a >= 0 ==> FactorialSteps(a) <= a + 2
  ensures a < 0 ==> FactorialSteps(a) <= 1
  decreases if a < 0 then 0 else a
{
  if a > 0 { FactorialStepsBound(a - 1); }
}

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 0
  ensures steps <= 6 * n + 30
{
  steps := 1;
  var rawN := n + 1;
  steps := steps + 1;
  var half := FloorDiv(rawN, 2);
  steps := steps + 1;

  var fRawN := Factorial(rawN);
  ghost var sRawN := FactorialSteps(rawN);
  steps := steps + sRawN;
  var fHalfM1a := Factorial(half - 1);
  ghost var sHalfM1 := FactorialSteps(half - 1);
  steps := steps + sHalfM1;
  var fHalfM1b := Factorial(half - 1);
  steps := steps + sHalfM1;

  var numerator := fRawN * fHalfM1a * fHalfM1b;
  steps := steps + 2;

  var fHalfA := Factorial(half);
  ghost var sHalf := FactorialSteps(half);
  steps := steps + sHalf;
  var fHalfB := Factorial(half);
  steps := steps + sHalf;
  var denom := fHalfA * fHalfB;
  steps := steps + 1;

  var step := FloorDiv(numerator, denom);
  steps := steps + 1;

  output := IntToString(FloorDiv(step, 2));
  steps := steps + 2;

  FactorialStepsBound(rawN);
  FactorialStepsBound(half - 1);
  FactorialStepsBound(half);
}

function Factorial(a: int): int
  ensures Factorial(a) >= 1
  decreases if a < 0 then 0 else a
{
  if a <= 0 then 1 else a * Factorial(a - 1)
}
