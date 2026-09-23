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

ghost function SumLen(xs: seq<string>): nat
{
  if |xs| == 0 then 0 else |xs[0]| + SumLen(xs[1..])
}

lemma SumLenSnocOne(xs: seq<string>, extra: string)
  requires |extra| == 1
  ensures SumLen(xs + [extra]) == SumLen(xs) + 1
  decreases |xs|
{
  if |xs| == 0 {
  } else {
    assert (xs + [extra])[1..] == xs[1..] + [extra];
    SumLenSnocOne(xs[1..], extra);
  }
}

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires 0 <= n <= |pairs|
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2
  ensures steps <= 8 * n + 3
{
  var sa := 0;
  var sg := 0;
  var pieces: seq<string> := [];
  var i := 0;
  steps := 1;
  while i < n
    invariant 0 <= i <= n
    invariant |pieces| == i
    invariant SumLen(pieces) == i
    invariant steps <= 1 + 5 * i
    decreases n - i
  {
    var a := pairs[i][0];
    var g := pairs[i][1];
    steps := steps + 2;
    if sa - sg + a <= 500 {
      SumLenSnocOne(pieces, "A");
      pieces := pieces + ["A"];
      sa := sa + a;
    } else {
      SumLenSnocOne(pieces, "G");
      pieces := pieces + ["G"];
      sg := sg + g;
    }
    steps := steps + 2;
    i := i + 1;
    steps := steps + 1;
  }
  output := Join(pieces, "");
  steps := steps + SumLen(pieces) + |pieces| + 1;
}
