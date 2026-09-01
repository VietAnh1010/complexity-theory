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
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var pts := points_list[i];
    var x1 := pts[0]; var y1 := pts[1]; var x2 := pts[2]; var y2 := pts[3];
    var x3 := pts[4]; var y3 := pts[5]; var x4 := pts[6]; var y4 := pts[7];
    var cross := (x2 - x1) * (y4 - y3) - (x4 - x3) * (y2 - y1);
    var absCross := if cross < 0.0 then -cross else cross;
    if absCross < 0.0000000001 {
      lines := lines + ["YES"];
    } else {
      lines := lines + ["NO"];
    }
    i := i + 1;
  }
  output := Join(lines, "\n") + "\n";
}
