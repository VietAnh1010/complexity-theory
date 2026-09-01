// 1101_A. Minimum Integer  (problem 1548, solution 1548_552)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import ceil
// n = int(input())
// 
// for i in range(n):
//     [l, r, d] = [int(j) for j in input().split()]
//     if l>d:
//         print(d)
//     else:
//         k = ceil(r/d)*d
//         print(k+d if k==r else k)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges_list: seq<seq<int>>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var row := edges_list[i];
    var l := row[0];
    var r := row[1];
    var d := row[2];
    var line: string;
    if l > d {
      line := IntToString(d);
    } else {
      var k := FloorDiv(r + d - 1, d) * d;
      if k == r {
        line := IntToString(k + d);
      } else {
        line := IntToString(k);
      }
    }
    lines := lines + [line];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
