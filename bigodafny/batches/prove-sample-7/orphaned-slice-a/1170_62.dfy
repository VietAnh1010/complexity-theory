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
// ("Tidak Tidak Tidak Tidak\n") — a constant independent of the input — so
// the sum over all lines is O(|matrices|), which is what the Join charge
// needs.
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
  ensures steps <= 50 * |matrices| + 3
{
  var parts: seq<string> := [];
  var idx := 0;
  steps := 1;
  while idx < |matrices|
    invariant 0 <= idx <= |matrices|
    invariant |parts| == idx
    invariant SumLen(parts) <= 24 * idx
    invariant steps <= 1 + 20 * idx
    decreases |matrices| - idx
  {
    var l := matrices[idx];
    var a := l[0];
    var b := l[1];
    var c := l[2];
    var d := l[3];
    var k0 := "Tidak";
    var k1 := "Tidak";
    var k2 := "Tidak";
    var k3 := "Tidak";
    steps := steps + 8;
    if (a + b) % 2 == 0 {
      if b + c != 0 { k2 := "Ya"; }
      if a + d != 0 { k3 := "Ya"; }
    } else {
      if b + c != 0 { k1 := "Ya"; }
      if a + d != 0 { k0 := "Ya"; }
    }
    steps := steps + 4;
    var line := k0 + " " + k1 + " " + k2 + " " + k3 + "\n";
    steps := steps + 7;
    assert |line| <= 24;
    SumLenSnoc(parts, line);
    parts := parts + [line];
    idx := idx + 1;
    steps := steps + 1;
  }
  output := Join(parts, "");
  steps := steps + SumLen(parts) + |parts| + 1;
}
