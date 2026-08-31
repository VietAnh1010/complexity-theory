// 514_B. Han Solo and Lazer Gun  (problem 1027, solution 1027_458)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, x1, y1 = [int(s) for s in input().split()] 
// slope = {}
// shoot=0
// for i in range(n):
//     x2,y2=[int(s) for s in input().split()]
//     if(x2-x1)==0:
//         m="a"
//     else:
//         m = (y2-y1)/(x2-x1)
//     
//     if m not in slope:
//         shoot+=1
//         slope[m] = 0
// print(shoot)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<(int, int)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
