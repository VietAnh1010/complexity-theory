// p02293 Parallel/Orthogonal  (problem 2183, solution 2183_2)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// q=int(input())
// 
// for _ in [0]*q:
//     x0,y0,x1,y1,x2,y2,x3,y3=map(int,input().split())
//     a1=x1-x0
//     a2=x3-x2
//     b1=y1-y0
//     b2=y3-y2
//     parallel=a1*b2-a2*b1
//     orthogonal=a1*a2+b1*b2
//     if parallel==0:
//         print("2")
//     elif orthogonal==0:
//         print("1")
//     else:
//         print("0")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, rows: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
