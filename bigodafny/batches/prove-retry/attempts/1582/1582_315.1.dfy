// 1582_315 -- complexity proof (ghost step counter)
include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: int, v_1: string) returns (output: string, ghost steps: nat)
  requires v_0 >= 1
  requires forall k :: 0 <= k < |v_1| ==> 'a' <= v_1[k] <= 'z'
  ensures steps <= 8 * |v_1| + 26 * (15 + 2 * |v_1|) + 40 + |output|
{
  steps := 27;
  var counts: seq<int> := seq(26, i => 0);
  var idx := 0;
  while idx < |v_1|
    invariant 0 <= idx <= |v_1|
    invariant |counts| == 26
    invariant forall k :: 0 <= k < 26 ==> 0 <= counts[k] <= idx
    invariant steps == 27 + 8 * idx
    decreases |v_1| - idx
  {
    var c := v_1[idx];
    var pos := (c as int) - ('a' as int);
    counts := counts[pos := counts[pos] + 1];
    idx := idx + 1;
    steps := steps + 8;
  }
  var ok := true;
  var restring: string := "";
  var ci := 0;
  while ci < 26
    invariant 0 <= ci <= 26
    invariant |counts| == 26
    invariant forall k :: 0 <= k < 26 ==> 0 <= counts[k] <= |v_1|
    invariant steps <= 27 + 8 * |v_1| + ci * (15 + 2 * |v_1|)
    decreases 26 - ci
  {
    ghost var before := steps;
    if ok && counts[ci] > 0 {
      if counts[ci] % v_0 != 0 {
        ok := false;
        steps := steps + 8;
      } else {
        restring := restring + Repeat([(('a' as int + ci) as char)], counts[ci] / v_0);
        steps := steps + 15 + 2 * (counts[ci] / v_0);
      }
    } else {
      steps := steps + 4;
    }
    CostMulDistrib(ci, 1, ci + 1, 15 + 2 * |v_1|);
    ci := ci + 1;
  }
  if ok {
    output := Repeat(restring, v_0);
    steps := steps + |output| + 1;
  } else {
    output := "-1";
  }
}
