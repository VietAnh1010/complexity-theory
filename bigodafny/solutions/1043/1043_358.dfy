// 1326_A. Bad Ugly Numbers  (problem 1043, solution 1043_358)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// for _ in range(n):
//     v = int(input())
//     if v == 1:
//         print(-1)
//     else:
//         print("2" + "3" * (v - 1))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    var v := a_list[i];
    if v == 1 {
      lines := lines + ["-1"];
    } else if v >= 2 {
      lines := lines + ["2" + Repeat("3", v - 1)];
    } else {
      lines := lines + ["2"];
    }
    i := i + 1;
  }
  output := Join(lines, "\n");
}
