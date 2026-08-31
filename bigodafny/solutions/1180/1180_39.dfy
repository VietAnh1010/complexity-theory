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
  var x := [1];
  var i := 0;
  while i < a
    decreases a - i
  {
    x := x + [x[|x|-1] + c_list[i]];
    i := i + 1;
  }
  var lines: seq<string> := [];
  i := 0;
  while i < b
    decreases b - i
  {
    var v := d_list[i];
    var cnt := 0;
    var j := 0;
    while j < |x|
      decreases |x| - j
    {
      if x[j] <= v { cnt := cnt + 1; }
      j := j + 1;
    }
    var idx := cnt - 1;
    lines := lines + [IntToString(idx + 1) + " " + IntToString(v - x[idx] + 1)];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
