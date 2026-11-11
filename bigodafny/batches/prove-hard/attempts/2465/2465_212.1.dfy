// --- Python ---------------------------------------------------------
// n = int(input())
//
// a = [int(x) for x in input().split()]
//
// a.sort(reverse=True)
//
// mask = 2**30
// while mask and len([ai for ai in a if ai & mask])!=1:
//     mask>>=1
// for i in range(n):
//     if mask&a[i]:
//         break
// a[i], a[0] = a[0], a[i]
// print (*a)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

lemma MergeElems<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
  ensures forall x :: x in Merge(a, b, less) ==> x in a || x in b
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
  } else if less(b[0], a[0]) {
    MergeElems(a, b[1..], less);
  } else {
    MergeElems(a[1..], b, less);
  }
}

lemma SortElems<T>(s: seq<T>, less: (T, T) -> bool)
  ensures forall x :: x in Sort(s, less) ==> x in s
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortElems(s[..|s| / 2], less);
    SortElems(s[|s| / 2..], less);
    MergeElems(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
  }
}

ghost function Pow2(k: nat): nat
  decreases k
{
  if k == 0 then 1 else 2 * Pow2(k - 1)
}

lemma Pow2At31()
  ensures Pow2(31) == 2147483648
{
  assert Pow2(0) == 1;
  assert Pow2(1) == 2;
  assert Pow2(2) == 4;
  assert Pow2(3) == 8;
  assert Pow2(4) == 16;
  assert Pow2(5) == 32;
  assert Pow2(6) == 64;
  assert Pow2(7) == 128;
  assert Pow2(8) == 256;
  assert Pow2(9) == 512;
  assert Pow2(10) == 1024;
  assert Pow2(11) == 2048;
  assert Pow2(12) == 4096;
  assert Pow2(13) == 8192;
  assert Pow2(14) == 16384;
  assert Pow2(15) == 32768;
  assert Pow2(16) == 65536;
  assert Pow2(17) == 131072;
  assert Pow2(18) == 262144;
  assert Pow2(19) == 524288;
  assert Pow2(20) == 1048576;
  assert Pow2(21) == 2097152;
  assert Pow2(22) == 4194304;
  assert Pow2(23) == 8388608;
  assert Pow2(24) == 16777216;
  assert Pow2(25) == 33554432;
  assert Pow2(26) == 67108864;
  assert Pow2(27) == 134217728;
  assert Pow2(28) == 268435456;
  assert Pow2(29) == 536870912;
  assert Pow2(30) == 1073741824;
  assert Pow2(31) == 2147483648;
}

method Solve(t: int, n_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires t >= 1
  requires |n_list| == t
  requires forall v :: v in n_list ==> 0 <= v < 1073741824
  ensures steps <= 2 * NLogN(t) + 400 * t + 400 + 2 * |output|
{
  steps := 0;
  var n := t;
  steps := steps + SortCost(|n_list|);
  var a := Sort(n_list, (x: int, y: int) => x > y);
  SortElems(n_list, (x: int, y: int) => x > y);
  assert |a| == n;
  assert forall v :: v in a ==> 0 <= v < 1073741824;
  assert forall idx2 :: 0 <= idx2 < |a| ==> a[idx2] in a;
  assert forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 1073741824;
  SortCostWithin(n, n);
  Pow2At31();
  ghost var it: nat := 0;
  ghost var kk: nat := 7 * n + 5;
  var mask := 1073741824;
  while mask != 0
    invariant 0 <= mask <= 1073741824
    invariant |a| == n
    invariant forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 1073741824
    invariant it <= 31
    invariant mask < Pow2(31 - it)
    invariant steps <= SortCost(n) + it * kk
    decreases mask
  {
    ghost var sIn := steps;
    ghost var itOld := it;
    steps := steps + 2;
    var cnt := 0;
    var k := 0;
    ghost var s0 := steps;
    while k < n
      invariant 0 <= k <= n
      invariant 0 <= mask <= 1073741824
      invariant |a| == n
      invariant forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 1073741824
      invariant steps <= s0 + 7 * k
    {
      steps := steps + 2;
      steps := steps + (2 + 1);
      if BitAnd(a[k], mask) != 0 {
        steps := steps + 1;
        cnt := cnt + 1;
      }
      steps := steps + 1;
      k := k + 1;
    }
    steps := steps + 1;
    steps := steps + 1;
    if it == 31 { assert Pow2(0) == 1; }
    assert it <= 30;
    CostMulDistrib(it, 1, it + 1, kk);
    if cnt == 1 {
      it := it + 1;
      break;
    }
    steps := steps + 1;
    it := it + 1;
    mask := mask / 2;
    assert Pow2(31 - itOld) == 2 * Pow2(30 - itOld);
  }
  assert it <= 31 && steps <= SortCost(n) + it * kk;
  CostMulMonoLeft(it, 31, kk);
  assert steps <= SortCost(n) + 31 * kk;
  steps := steps + 1;
  steps := steps + 1;
  var i := n - 1;
  var found := false;
  var idx := 0;
  ghost var s2 := steps;
  while idx < n && !found
    invariant 0 <= idx <= n
    invariant 0 <= i < n
    invariant |a| == n
    invariant 0 <= mask <= 1073741824
    invariant forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 1073741824
    invariant steps <= s2 + 8 * idx
  {
    steps := steps + (3 + if idx < n then 1 else 0);
    steps := steps + (2 + 1);
    if BitAnd(a[idx], mask) != 0 {
      i := idx;
      found := true;
    }
    steps := steps + 1;
    idx := idx + 1;
  }
  steps := steps + (2 + if idx < n then 1 else 0);
  steps := steps + 1;
  var tmp := a[0];
  assert 0 <= i < |a|;
  steps := steps + 3;
  a := a[0 := a[i]][i := tmp];
  steps := steps + n;
  var parts := seq(n, _ /* _v0 */ => "");
  var p := 0;
  ghost var s3 := steps;
  ghost var d: nat := 0;
  assert parts[..0] == [];
  while p < n
    invariant 0 <= p <= n
    invariant |parts| == n
    invariant steps <= s3 + 5 * p + d
    invariant d == SumLen(parts[..p])
  {
    steps := steps + 2;
    steps := steps + (2 + Digits(a[p]));
    ghost var old := parts;
    parts := parts[p := IntToString(a[p])];
    IntToStringDigits(a[p]);
    SumLenSnoc(old[..p], IntToString(a[p]));
    assert parts[..p + 1] == old[..p] + [IntToString(a[p])];
    d := d + Digits(a[p]);
    steps := steps + 1;
    p := p + 1;
  }
  assert parts[..p] == parts;
  steps := steps + 1;
  steps := steps + (SumLen(parts) + |parts| + |"\n"|);
  output := Join(parts, " ") + "\n";
  JoinLen(parts, " ");
}

import opened Prelude
