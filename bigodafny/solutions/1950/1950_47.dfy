// 697_B. Barnicle  (problem 1950, solution 1950_47)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from decimal import *
// 
// while True :
//     try :
//         a=input()
//         b=Decimal(a)
// 
//         if(round(b)==b):
//             print ("%d"%b)
//         else:
//             print (b)
//     
//     except :
//         break
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(coefficient: real, exponent: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
