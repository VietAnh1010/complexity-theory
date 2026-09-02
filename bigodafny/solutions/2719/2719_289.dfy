// 245_A. System Administrator  (problem 2719, solution 2719_289)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [0, 0]
// b = [0, 0]
// for i in range(n):
//     t, x, y = (int(x) for x in input().split())
//     if t == 1:
//         a[0] += x
//         a[1] += y
//     else:
//         b[0] += x
//         b[1] += y
// if a[0] >= a[1]:
//     print('LIVE')
// else:
//     print('DEAD')
// if b[0] >= b[1]:
//     print('LIVE')
// else:
//     print('DEAD')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values_list: seq<seq<int>>) returns (output: string)
{
  var a0 := 0; var a1 := 0; var b0 := 0; var b1 := 0;
  var i := 0;
  while i < |values_list|
    invariant 0 <= i <= |values_list|
  {
    var row := values_list[i];
    if |row| >= 3 {
      if row[0] == 1 {
        a0 := a0 + row[1];
        a1 := a1 + row[2];
      } else {
        b0 := b0 + row[1];
        b1 := b1 + row[2];
      }
    }
    i := i + 1;
  }
  var line1 := if a0 >= a1 then "LIVE" else "DEAD";
  var line2 := if b0 >= b1 then "LIVE" else "DEAD";
  output := line1 + "\n" + line2;
}
