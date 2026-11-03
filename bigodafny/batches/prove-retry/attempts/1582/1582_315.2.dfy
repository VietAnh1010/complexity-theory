// 1582_315 -- complexity proof (ghost step counter)
include "../../../../prelude.dfy"

method Solve(v_0: int, v_1: string)
    returns (output: string, ghost steps: nat)
  requires v_0 >= 1
  requires forall k :: 0 <= k < |v_1| ==> 'a' <= v_1[k] <= 'z'
  ensures steps <= 11 * |v_1| + 26 * (16 + 2 * |v_1|) + 40 + |output|
{
  steps := 0;
  steps := steps + 26;
  var counts: seq<int> := seq(26, i => 0);
  var idx := 0;
  while idx < |v_1|
    invariant 0 <= idx <= |v_1|
    invariant |counts| == 26
    invariant forall k :: 0 <= k < 26 ==> 0 <= counts[k] <= idx
    invariant steps == 26 + 11 * idx
    decreases |v_1| - idx
  {
    steps := steps + 3;
    steps := steps + 1;
    var c := v_1[idx];
    steps := steps + 3;
    var pos := c as int - 'a' as int;
    steps := steps + 3;
    counts := counts[pos := counts[pos] + 1];
    steps := steps + 1;
    idx := idx + 1;
  }
  steps := steps + 2;
  var ok := true;
  var restring: string := "";
  var ci := 0;
  while ci < 26
    invariant 0 <= ci <= 26
    invariant |counts| == 26
    invariant forall k :: 0 <= k < 26 ==> 0 <= counts[k] <= |v_1|
    invariant steps <= 28 + 11 * |v_1| + ci * (16 + 2 * |v_1|)
    decreases 26 - ci
  {
    CostMulDistrib(ci, 1, ci + 1, 16 + 2 * |v_1|);
    steps := steps + 2;
    steps := steps + (1 + if ok then 2 else 0);
    if ok && counts[ci] > 0 {
      steps := steps + 3;
      if counts[ci] % v_0 != 0 {
        ok := false;
      } else {
        RepeatLen([('a' as int + ci) as char], counts[ci] / v_0);
        steps := steps + (6 + |[('a' as int + ci) as char]| * (counts[ci] / v_0) + |Repeat([('a' as int + ci) as char], counts[ci] / v_0)|);
        restring := restring + Repeat([('a' as int + ci) as char], counts[ci] / v_0);
      }
    }
    steps := steps + 1;
    ci := ci + 1;
  }
  steps := steps + 1;
  if ok {
    RepeatLen(restring, v_0);
    steps := steps + |restring| * v_0;
    output := Repeat(restring, v_0);
  } else {
    output := "-1";
  }
}

lemma RepeatLen(s: string, n: nat)
  ensures |Repeat(s, n)| == |s| * n
  decreases n
{
  if n > 0 { RepeatLen(s, n - 1); }
}

import opened Prelude
