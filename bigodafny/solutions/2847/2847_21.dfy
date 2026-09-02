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
  decreases *
{
  var x := a; var y := b;
  var curX := 0; var curY := 0;
  var i := 1;
  var pos := 0;
  var signX := [1, 0, -1, 0];
  var signY := [0, 1, 0, -1];
  var ans := 0;
  var j := 0;
  while curX != x || curY != y
    invariant 0 <= pos < 4
    decreases *
  {
    if j == i {
      j := 0;
      if pos % 2 == 1 { i := i + 1; }
      pos := (pos + 1) % 4;
      ans := ans + 1;
    }
    curX := curX + signX[pos];
    curY := curY + signY[pos];
    j := j + 1;
  }
  output := IntToString(ans);
}
