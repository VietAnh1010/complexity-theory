// 785_B. Anton and Classes  (problem 1177, solution 1177_9)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// c=[]
// for i in range(n):
//     c.append(list(map(int,input().split())))
// m=int(input())
// p=[]
// for i in range(m):
//     p.append(list(map(int,input().split())))
// c.sort()
// p.sort()
// ans=0
// for i in range(n):
//     ans=max(ans,p[-1][0]-c[i][1])
// for i in range(m):
//     ans=max(ans,c[-1][0]-p[i][1])
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, rectangles: seq<(int, int)>, m: int, checks: seq<(int, int)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
