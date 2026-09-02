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

method Solve(n: int) returns (output: string)
{
  var m := n - 1;
  var a1 := m + 5;
  var k1 := m;
  var c1 := FloorDiv(Factorial(a1), Factorial(k1) * Factorial(a1 - k1));
  var a2 := m + 3;
  var k2 := 3;
  var c2 := FloorDiv(Factorial(a2), Factorial(k2) * Factorial(a2 - k2));
  output := IntToString(c1 * c2);
}


function Factorial(a: int): int
  decreases if a < 0 then 0 else a
{
  if a <= 0 then 1 else a * Factorial(a - 1)
}
