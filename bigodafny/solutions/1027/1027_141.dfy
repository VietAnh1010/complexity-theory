// 514_B. Han Solo and Lazer Gun  (problem 1027, solution 1027_141)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import itertools
// 
// n, x0, y0 = [int(x) for x in input().split()]
// target = []
// for i in range(n):
//     x, y = [int(x) for x in input().split()]
//     cos2 = (x-x0)**2 / ((x-x0)**2 + (y-y0)**2)
//     target.append(cos2 if (x-x0)*(y-y0) >= 0 else -cos2)
// 
// target.sort()
// L = list(itertools.groupby(target))
// print(len(L))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<(int, int)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
