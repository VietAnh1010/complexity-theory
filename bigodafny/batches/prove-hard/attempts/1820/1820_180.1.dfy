// --- Python ---------------------------------------------------------
// n , x , y = map(int,input().split())
// arr = list(map(int,input().split()))
// 
// for i in range(n):
//     if i >= x :
//         if arr[i] == min(arr[i - x : i + y + 1]):
//             print(i + 1 )
//             break
//     else:
//         if arr[i] == min(arr[0 : i + y +1]):
//             print(i + 1 )
//             break
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(a: int, b: int, c: int, d_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires a <= |d_list|
  requires b >= 0
  requires c >= 0
  ensures steps <= (if a > 0 then a else 0) * (17 + b + c) + 3 + |output|
{
  steps := 0;
  ghost var nn: nat := if a > 0 then a else 0;
  ghost var kk: nat := 17 + b + c;
  ghost var it: nat := 0;
  MulZero(kk);
  var n := a;
  var x := b;
  var y := c;
  var arr := d_list;
  var i := 0;
  var found := false;
  var result := 0;
  while i < n && !found
    invariant 0 <= i
    invariant n == a && x == b && y == c && arr == d_list
    invariant it == i + (if found then 1 else 0)
    invariant i <= nn
    invariant found ==> i < nn
    invariant steps <= it * kk
    invariant found ==> result == i + 1
    decreases !found, n - i
  {
    ghost var s0 := steps;
    steps := steps + (3 + if i < n then 1 else 0);
    steps := steps + (2 + if i >= x then 1 else 0);
    var lo := if i >= x then i - x else 0;
    steps := steps + 2;
    var hi := i + y + 1;
    steps := steps + 2;
    if hi > |arr| {
      steps := steps + 1;
      hi := |arr|;
    }
    assert lo <= i;
    assert hi >= i + 1;
    steps := steps + (1 + |arr[lo .. hi]|);
    var m := MinSeq(arr[lo .. hi]);
    steps := steps + 2;
    if arr[i] == m {
      steps := steps + 1;
      result := i + 1;
      found := true;
    } else {
      steps := steps + 1;
      i := i + 1;
    }
    MulStep(it, kk);
    it := it + 1;
    assert steps <= s0 + kk;
  }
  MulMono(it, nn, kk);
  steps := steps + (2 + if i < n then 1 else 0);
  if found {
    IntToStringDigits(result);
    steps := steps + Digits(result);
    output := IntToString(result);
  } else {
    output := "";
  }
}

lemma MulZero(k: nat)
  ensures 0 * k == 0
{}

lemma MulStep(i: nat, k: nat)
  ensures (i + 1) * k == i * k + k
{}

lemma MulMono(i: nat, n: nat, k: nat)
  requires i <= n
  ensures i * k <= n * k
{}

import opened Prelude
