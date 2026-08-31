// p00021 Parallelism  (problem 522, solution 522_46)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// for i in range(n):
//     x1, y1, x2, y2, x3, y3, x4, y4 = map(float, input().split())
//     print('YES' if abs((x2 - x1)*(y4 - y3) - (x4 - x3)*(y2 - y1)) < 1e-10 else 'NO')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, points_list: seq<seq<real>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
