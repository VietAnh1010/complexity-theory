// 1130_B. Two Cakes  (problem 3033, solution 3033_146)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=[int(v) for v in input().split()]
// b=[[] for _ in range(n+1)]
// for i in range(2*n):
//     b[a[i]].append(i+1)
// f=b[1][0]+b[1][1]-2
// for j in range(1,n):
//     p=f+abs(b[j][0]-b[j+1][0])+abs(b[j][1]-b[j+1][1])
//     q=f+abs(b[j][0]-b[j+1][1])+abs(b[j][1]-b[j+1][0])
//     f=min(p,q)
// print(f)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
