// 889_A. Petya and Catacombs  (problem 1367, solution 1367_59)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// di = {0 : 0}
// k = 1
// q = 1
// for i in a:
//     if i in di:
//         del di[i]
//     else:
//         q += 1
//     di[k] = i
//     k += 1
// print(q)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<int>) returns (output: string)
{
  var di: map<int, int> := map[0 := 0];
  var k := 1;
  var q := 1;
  var idx := 0;
  while idx < |coordinates|
    decreases |coordinates| - idx
  {
    var iv := coordinates[idx];
    if iv in di {
      di := di - {iv};
    } else {
      q := q + 1;
    }
    di := di[k := iv];
    k := k + 1;
    idx := idx + 1;
  }
  output := IntToString(q);
}
