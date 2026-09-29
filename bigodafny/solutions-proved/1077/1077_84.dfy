// 630_G. Challenge Pennants  (problem 1077, solution 1077_84)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def Fact(n):
//   res = 1 
//   while n > 0 :
//     res *= n
//     n -= 1
//   return res
// 
// def C(n,k):
//   return (Fact(n) // ( Fact(k) * Fact(n-k) ) )
//   
// n = int ( input() ) - 1 
// 
// print ( C(n+5,n)*C(n+3,3) )
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Factorial's charge: one step per recursive call, as the Python's
// `while n > 0: res *= n; n -= 1` runs one iteration per call.
ghost function FactorialSteps(a: int): nat
  decreases if a < 0 then 0 else a + 1
{
  if a <= 0 then 1 else 1 + FactorialSteps(a - 1)
}

lemma FactorialStepsBound(a: int)
  ensures FactorialSteps(a) <= (if a > 0 then a else 0) + 2
  decreases if a < 0 then 0 else a
{
  if a > 0 { FactorialStepsBound(a - 1); }
}

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * (if n > 0 then n else 0) + |output| + 40
{
  var m := n - 1;
  var a1 := m + 5;
  var k1 := m;
  var c1 := FloorDiv(Factorial(a1), Factorial(k1) * Factorial(a1 - k1));
  var a2 := m + 3;
  var k2 := 3;
  var c2 := FloorDiv(Factorial(a2), Factorial(k2) * Factorial(a2 - k2));
  output := IntToString(c1 * c2);
  FactorialStepsBound(a1);
  FactorialStepsBound(k1);
  FactorialStepsBound(a1 - k1);
  FactorialStepsBound(a2);
  FactorialStepsBound(k2);
  FactorialStepsBound(a2 - k2);
  steps := FactorialSteps(a1) + FactorialSteps(k1) + FactorialSteps(a1 - k1)
         + FactorialSteps(a2) + FactorialSteps(k2) + FactorialSteps(a2 - k2)
         + |output| + 10;
}


function Factorial(a: int): int
  ensures Factorial(a) >= 1
  decreases if a < 0 then 0 else a
{
  if a <= 0 then 1 else a * Factorial(a - 1)
}
