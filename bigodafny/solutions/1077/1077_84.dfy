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
  output := ""; // TODO: translate the Python above
}
