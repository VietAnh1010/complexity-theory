// 279_A. Point on Spiral  (problem 2847, solution 2847_21)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x, y = map(int, input().split())
// 
// cur_x, cur_y = 0, 0
// i = 1
// pos = 0
// sign = [(1, 0), (0, 1), (-1, 0), (0, -1)]
// ans = 0
// j = 0
// while cur_x != x or cur_y != y:
//      if j == i:
//           j = 0
//           if pos % 2 == 1:
//                i += 1
//           pos = (pos + 1) % 4
//           ans += 1     
//      
//      cur_x = cur_x + sign[pos][0]
//      cur_y = cur_y + sign[pos][1]
//      j += 1
// 
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
