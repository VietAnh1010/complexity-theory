// 1425_H. Huge Boxes of Animal Toys  (problem 1170, solution 1170_62)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
//
// for tc in range(t):
//
//     a, b, c, d = map(int, input().split())
//
//     k = ["Tidak"] * 4
//
//     if not (a+b) % 2:
//         if (b+c):
//             k[2] = "Ya"
//         if (a+d):
//             k[3] = "Ya"
//     else:
//         if (b+c):
//             k[1] = "Ya"
//         if (a+d):
//             k[0] = "Ya"
//
//     print(*k)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Every emitted line has length between 12 ("Ya Ya Ya Ya\n") and 24
// ("Tidak Tidak Tidak Tidak\n"): a constant independent of the input, so
// SumLen(parts) is O(|matrices|), which is what Join's charge needs.
ghost function SumLen(xs: seq<string>): nat
{
  if |xs| == 0 then 0 else |xs[0]| + SumLen(xs[1..])
}

lemma SumLenSnoc(xs: seq<string>, extra: string)
  ensures SumLen(xs + [extra]) == SumLen(xs) + |extra|
  decreases |xs|
{
  if |xs| == 0 {
  } else {
    assert (xs + [extra])[1..] == xs[1..] + [extra];
    SumLenSnoc(xs[1..], extra);
  }
}

method Solve(n: int, matrices: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires forall i :: 0 <= i < |matrices| ==> |matrices[i]| >= 4
  ensures steps <= 100 * |matrices| + 5
{
  var parts: seq<string> := [];
  var idx := 0;
  steps := 1;
  while idx < |matrices|
    invariant 0 <= idx <= |matrices|
    invariant steps <= 60 * idx + 1
    invariant |parts| == idx
    invariant SumLen(parts) <= 24 * idx
    decreases |matrices| - idx
  {
    var l := matrices[idx];
    var a := l[0];
    var b := l[1];
    var c := l[2];
    var d := l[3];
    steps := steps + 4;
    var k0 := "Tidak";
    var k1 := "Tidak";
    var k2 := "Tidak";
    var k3 := "Tidak";
    if (a + b) % 2 == 0 {
      steps := steps + 3;
      if b + c != 0 { k2 := "Ya"; }
      steps := steps + 2;
      if a + d != 0 { k3 := "Ya"; }
      steps := steps + 2;
    } else {
      steps := steps + 3;
      if b + c != 0 { k1 := "Ya"; }
      steps := steps + 2;
      if a + d != 0 { k0 := "Ya"; }
      steps := steps + 2;
    }
    assert |k0| <= 5 && |k1| <= 5 && |k2| <= 5 && |k3| <= 5;
    var line := k0 + " " + k1 + " " + k2 + " " + k3 + "\n";
    steps := steps + 35;
    assert |line| <= 24;
    SumLenSnoc(parts, line);
    parts := parts + [line];
    steps := steps + 1;
    idx := idx + 1;
  }
  output := Join(parts, "");
  steps := steps + SumLen(parts) + |parts| + 1;
}
