// 1077_A. Frog Jumping  (problem 2124, solution 2124_2)
// time complexity: O(n)
// python exact-diff baseline: partial

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, queries: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |queries| ==> |queries[k]| >= 3
  ensures steps <= 8 * |queries| + 3
{
  steps := 1;
  var answer: seq<int> := [];
  var i := 0;
  while i < |queries|
    invariant 0 <= i <= |queries|
    invariant |answer| == i
    invariant steps <= 6 * i + 1
    decreases |queries| - i
  {
    var a1 := queries[i][0];
    var b1 := queries[i][1];
    var k := queries[i][2];
    var kk := FloorDiv(k, 2);
    var val := if k % 2 == 1 then kk * (a1 - b1) + a1 else kk * (a1 - b1);
    answer := answer + [val];
    i := i + 1;
    steps := steps + 6;
  }
  var parts := seq(|answer|, j requires 0 <= j < |answer| => IntToString(answer[j]));
  steps := steps + |answer|;
  output := if |parts| == 0 then "" else Join(parts, "\n") + "\n";
  steps := steps + |parts| + 1;
}
