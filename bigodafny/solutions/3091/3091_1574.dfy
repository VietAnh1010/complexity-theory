// 467_A. George and Accommodation  (problem 3091, solution 3091_1574)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// 
// count=0
// for i in range(n):
//     p,q = map(int,input().split())
//     if p<q and (q-p)>=2:
//         count+=1
// 
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs_list: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
