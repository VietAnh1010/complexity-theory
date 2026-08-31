// 279_A. Point on Spiral  (problem 2847, solution 2847_45)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// '''l = [[(0, 0), (1, 0)],
//      [(1, 0), (1, 1)],
//      [(1, 1), (-1, 1)],
//      [(-1, 1), (-1, -1)],
//      [(-1, - 1), (2, -1)],
//      [(2, -1), (2, 2)]]
// '''
// '''
// pattern er shudhone na paria
// last e net theke copy marcha
// pattern copy marcha re.
// '''
// x,y = map(int, input().split())
// if y >= x and y < -x:
//     print(-4*x-1)
// elif y > x and y >= -x:
//     print(4*y-2)
// elif y <= x and y > 1-x:
//     print(4*x-3)
// elif y < x and y <= 1-x:
//     print(-4*y)
// else:
//     print(0)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
