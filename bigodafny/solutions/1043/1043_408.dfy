// 1326_A. Bad Ugly Numbers  (problem 1043, solution 1043_408)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// t = int(input())
// while t:
//     n = int(input())
//     if n >= 2:    
//         print('23',end="")
//     else: 
//         print("-1")
//     while n>2:
//         print('3',end="")
//         n -= 1
//     print(" ")
//     t -= 1
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
