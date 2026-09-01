// 667_B. Coat of Anticubism  (problem 2071, solution 2071_33)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// data = [int(i) for i in input().split()]
// mx, box = 0, 0
// for i in data:
//     if i > mx:
//         box += mx
//         mx = i
//     else:
//         box += i
// print(mx - box + 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var data := a_list;
  var mx := 0;
  var box := 0;
  var idx := 0;
  while idx < |data|
    decreases |data| - idx
  {
    var i := data[idx];
    if i > mx {
      box := box + mx;
      mx := i;
    } else {
      box := box + i;
    }
    idx := idx + 1;
  }
  output := IntToString(mx - box + 1);
}
