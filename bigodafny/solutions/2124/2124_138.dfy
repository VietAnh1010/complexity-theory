// 1077_A. Frog Jumping  (problem 2124, solution 2124_138)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// all_data = []
// 
// for i in range(t):
//     data = [int(i) for i in input().split(" ")]
//     all_data.append(data)
// 
// for i in all_data:
//     right = i[0]
//     left = i[1]
//     k = i[2]
//     jump = right-left
//     if k % 2 == 0:
//         print(jump*(k//2))
//     else:
//         print(jump*(k//2)+right)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, queries: seq<seq<int>>) returns (output: string)
  requires forall k :: 0 <= k < |queries| ==> |queries[k]| >= 3
{
  var parts: seq<string> := [];
  var i := 0;
  while i < |queries|
  {
    var right := queries[i][0];
    var left := queries[i][1];
    var k := queries[i][2];
    var jump := right - left;
    var kk := FloorDiv(k, 2);
    var val := if k % 2 == 0 then jump * kk else jump * kk + right;
    parts := parts + [IntToString(val)];
    i := i + 1;
  }
  output := if |parts| == 0 then "" else Join(parts, "\n") + "\n";
}
