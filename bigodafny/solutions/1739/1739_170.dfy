// 854_A. Fraction  (problem 1739, solution 1739_170)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n=int(input())
// if (n%2)!=0:
//     a=1
//     while a < math.floor(n/2):
//         a+=1
//     b=n-a 
//     print(f"{a}  {b}")
// else:
//     a=1
//     while a < math.floor(n/2)-1:
//         a+=1
//     b=n-a 
//     if a%2==0 and b%2==0:
//         a=a-1
//         b=b+1
//     print(f"{a}  {b}")
//     
//     
//     
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(number: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
