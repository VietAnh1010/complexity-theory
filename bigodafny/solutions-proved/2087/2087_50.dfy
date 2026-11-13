include "../../prelude.dfy"
import opened Prelude

method Solve(strings: seq<string>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |strings| ==> |strings[k]| >= 1
  ensures steps <= 13 * SumLen(strings) + 1100 * |strings| + 5 + |output|
{
  steps := 3;
  var alphabet := "abcdefghijklmnopqrstuvwxyz";
  var results: seq<string> := [];
  var si := 0;
  while si < |strings|
    invariant 0 <= si <= |strings|
    invariant |results| == si
    invariant steps <= 13 * SumLen(strings[..si]) + 1100 * si + 3
    decreases |strings| - si
  {
    var a := strings[si];
    var s := "";
    ghost var L := |a|;
    ghost var base := steps;
    steps := steps + 4;
    while |a| != 1
      invariant |a| >= 1
      invariant |a| <= L
      invariant |s| == L - |a|
      invariant steps <= base + 4 + 10 * (L - |a|)
      decreases |a|
    {
      if a[0] > a[|a| - 1] {
        s := s + [a[0]];
        a := a[1..];
        steps := steps + 10;
      } else {
        s := s + [a[|a| - 1]];
        a := a[..|a| - 1];
        steps := steps + 10;
      }
    }
    s := s + "a";
    steps := steps + 2 + 2 * |s|;
    var rev: string := seq(|s|, i requires 0 <= i < |s| => s[|s| - 1 - i]);
    ghost var base2 := steps;
    var found := false;
    var start := 0;
    while start + |rev| <= |alphabet| && !found
      invariant 0 <= start <= |alphabet|
      invariant steps <= base2 + 40 * start
      decreases |alphabet| - start
    {
      if alphabet[start..start + |rev|] == rev {
        found := true;
      }
      start := start + 1;
      steps := steps + 40;
    }
    steps := steps + 6;
    if a != "a" || !found {
      results := results + ["NO"];
    } else {
      results := results + ["YES"];
    }
    SumLenSnoc(strings[..si], strings[si]);
    assert strings[..si + 1] == strings[..si] + [strings[si]];
    si := si + 1;
    steps := steps + 1;
  }
  output := Join(results, "\n");
  steps := steps + SumLen(results) + |results|;
  assert strings[..si] == strings;
  if |results| > 0 { JoinLen(results, "\n"); }
}
