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
  var n := number;
  var a := 1;
  var b := 0;
  if n % 2 != 0 {
    var half := FloorDiv(n, 2);
    while a < half
      decreases half - a
    {
      a := a + 1;
    }
    b := n - a;
  } else {
    var half := FloorDiv(n, 2) - 1;
    while a < half
      decreases half - a
    {
      a := a + 1;
    }
    b := n - a;
    if a % 2 == 0 && b % 2 == 0 {
      a := a - 1;
      b := b + 1;
    }
  }
  output := IntToString(a) + "  " + IntToString(b);
}
