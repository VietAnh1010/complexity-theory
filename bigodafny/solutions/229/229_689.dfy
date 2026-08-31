// 677_A. Vanya and Fence  (problem 229, solution 229_689)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a,b=map(int,input().split())
// c=map(int,input().split())
// d=0
// for i in c:
//     if i>b:
//         d+=2
//     else:
//         d+=1
// print(d)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
