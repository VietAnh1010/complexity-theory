// 282_B. Painting Eggs  (problem 1673, solution 1673_129)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// sa,sg=0,0
// ans=''
// for _ in range(int(input())):
//     a,g=map(int,input().split())
//     if sa-sg+a<=500:
//         ans+='A'
//         sa+=a
//     else:
//         ans+='G'
//         sg+=g
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Each emitted piece is a single-character string ("A" or "G"), so
// SumLen(pieces) == |pieces|, which is what Join's charge needs.
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

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires 0 <= n <= |pairs|
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2
  ensures steps <= 10 * n + 5
{
  var sa := 0;
  var sg := 0;
  var pieces: seq<string> := [];
  var i := 0;
  steps := 1;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= 8 * i + 1
    invariant |pieces| == i
    invariant SumLen(pieces) == i
    decreases n - i
  {
    var a := pairs[i][0];
    var g := pairs[i][1];
    steps := steps + 2;
    if sa - sg + a <= 500 {
      SumLenSnoc(pieces, "A");
      pieces := pieces + ["A"];
      sa := sa + a;
      steps := steps + 4;
    } else {
      SumLenSnoc(pieces, "G");
      pieces := pieces + ["G"];
      sg := sg + g;
      steps := steps + 4;
    }
    i := i + 1;
    steps := steps + 1;
  }
  output := Join(pieces, "");
  steps := steps + SumLen(pieces) + |pieces| + 1;
}
