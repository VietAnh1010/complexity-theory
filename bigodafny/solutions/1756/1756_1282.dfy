// 155_A. I_love_%username%  (problem 1756, solution 1756_1282)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// m=int(input())
// x=[int(x) for x in input().split()]
// if(m==1):
//   print(0)
// else:
//   maximum=x[0]
//   minimum=x[0]
//   count=0
//   for i in x:
//     if(i<minimum):
//       count=count+1
//       minimum=i
// 
//     if(i>maximum):
//       count=count+1
//       maximum=i
// 
// 
//   print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
