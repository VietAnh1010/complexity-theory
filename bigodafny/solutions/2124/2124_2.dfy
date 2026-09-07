// 1077_A. Frog Jumping  (problem 2124, solution 2124_2)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// answer = []
// for i in range(t):
//     a, b, k = map(int, input().split())
//     if k % 2 == 1:
//         answer.append(k // 2 * (a - b) + a)
//     else:
//         answer.append(k // 2 * (a - b))
// for i in range(t):
//     print(answer[i])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, queries: seq<seq<int>>) returns (output: string)
  requires forall k :: 0 <= k < |queries| ==> |queries[k]| >= 3
{
  var answer: seq<int> := [];
  var i := 0;
  while i < |queries|
  {
    var a1 := queries[i][0];
    var b1 := queries[i][1];
    var k := queries[i][2];
    var kk := FloorDiv(k, 2);
    var val := if k % 2 == 1 then kk * (a1 - b1) + a1 else kk * (a1 - b1);
    answer := answer + [val];
    i := i + 1;
  }
  var parts := seq(|answer|, j requires 0 <= j < |answer| => IntToString(answer[j]));
  output := if |parts| == 0 then "" else Join(parts, "\n") + "\n";
}
