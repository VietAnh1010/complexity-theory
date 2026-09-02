// 1102_C. Doors Breaking and Repairing  (problem 2982, solution 2982_323)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import ceil
// n, x, y = map(int, input().split())
// li = list(map(int, input().split()))
// if x > y:
//     print(len(li))
// else:
//     num = 0
//     for i in li:
//         if i <= x:
//             num += 1
//     print(ceil(num / 2))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string)
{
  var x := b;
  var y := c;
  if x > y {
    output := IntToString(|d_list|);
  } else {
    var num := 0;
    var i := 0;
    while i < |d_list|
      invariant 0 <= i <= |d_list|
      invariant num >= 0
      decreases |d_list| - i
    {
      if d_list[i] <= x { num := num + 1; }
      i := i + 1;
    }
    output := IntToString((num + 1) / 2);
  }
}
