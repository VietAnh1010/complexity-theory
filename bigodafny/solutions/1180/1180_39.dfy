// 978_C. Letters  (problem 1180, solution 1180_39)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from bisect import bisect
// n, m = map(int, input().split())
// x = [1]
// for v in map(int, input().split()):
//     x.append(x[-1] + v)
// for v in map(int, input().split()):
//     i = bisect(x, v) - 1
//     print(i+1, v-x[i]+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
