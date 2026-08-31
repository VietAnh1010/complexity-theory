// 451_A. Game With Sticks  (problem 536, solution 536_1054)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// r, c = map(int, input().split())
// t = r*c
// 
// 
// 
// i = 0
// while t !=0:
//     r = r-1
//     c=c-1
//     t = r*c
//     i += 1
// 
// 
//     
// if i%2 == 0:
//     print("Malvika")
// else:
//     print("Akshat")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
