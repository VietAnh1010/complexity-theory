// 1187_A. Stickers and Toys  (problem 1231, solution 1231_51)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for i in range(t):
//     l=list(map(int,input().split()))
//     print(max(l[0]-l[1],l[0]-l[2])+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
