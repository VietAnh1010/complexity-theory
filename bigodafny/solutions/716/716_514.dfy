// 1047_B. Cover Points  (problem 716, solution 716_514)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// d = int(input())
// 
// verts = []
// 
// for i in range(d):
//     d = [int(x) for x in input().split(' ')]
//     verts.append(d)
// 
// maxx = 0
// for v in verts:
//     maxx = max(maxx, v[0] + v[1])
// 
// print(maxx)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
