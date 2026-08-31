// 263_A. Beautiful Matrix  (problem 531, solution 531_3456)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// col=row=1
// 
// for i in range (0,5):
//     a=list(input().split())
//     if(len(set(a))==1): row+=1
//     else: col=a.index('1')+1 ; break
// 
// print(abs(3-row)+abs(3-col))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(matrix: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
