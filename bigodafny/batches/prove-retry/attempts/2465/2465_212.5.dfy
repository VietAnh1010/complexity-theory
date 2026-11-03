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

ghost function Lg(x: nat): nat  decreases x
{ if x == 0 then 0 else 1 + Lg(x / 2) }

ghost function Pw(k: nat): nat
{ if k == 0 then 1 else 2 * Pw(k - 1) }

lemma LgPw(x: nat, k: nat)
  requires x < Pw(k)
  ensures Lg(x) <= k
  decreases k
{
  if x > 0 { LgPw(x / 2, k - 1); }
}

lemma Lg30()
  ensures Lg(0x40000000) <= 31
{
  assert Pw(8) == 256;
  assert Pw(16) == 65536 by { assert Pw(16) == 256 * 256 by { PwAdd(8, 8); } }
  assert Pw(31) == 0x80000000 by { PwAdd(16, 15); PwAdd(8, 7); PwAdd(4, 3); assert Pw(3) == 8; assert Pw(4) == 16; }
  LgPw(0x40000000, 31);
}

lemma PwAdd(a: nat, b: nat)
  ensures Pw(a + b) == Pw(a) * Pw(b)
  decreases a
{
  if a > 0 { PwAdd(a - 1, b); }
}

method Solve(t: int, n_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires t >= 1
  requires |n_list| == t
  requires forall v :: v in n_list ==> 0 <= v < 1073741824
  ensures steps <= 2 * NLogN(t) + 240 * t + 2 * |output| + 200
{
  steps := 0;
  var n := t;
  steps := steps + SortCost(|n_list|);
  var a := Sort(n_list, (x: int, y: int) => x > y);
  SortCostWithin(n, n);
  SortIsPermutation(n_list, (x: int, y: int) => x > y);
  SortElems(n_list, (x: int, y: int) => x > y);
  assert |a| == n;
  assert forall v :: v in a ==> 0 <= v < 1073741824;
  assert forall idx2 :: 0 <= idx2 < |a| ==> a[idx2] in a;
  assert forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 1073741824;
  var mask := 1073741824;
  Lg30();
  ghost var iters: nat := 0;
  ghost var b0 := steps;
  while mask != 0
    invariant 0 <= mask <= 1073741824
    invariant |a| == n
    invariant forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 1073741824
    invariant iters + Lg(mask) <= 31
    invariant steps <= b0 + iters * (7 * n + 5)
    decreases mask
  {
    steps := steps + 2;
    var cnt := 0;
    var k := 0;
    ghost var b1 := steps;
    while k < n
      invariant 0 <= k <= n
      invariant 0 <= mask <= 1073741824
      invariant |a| == n
      invariant forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 1073741824
      invariant steps <= b1 + 7 * k
      decreases n - k
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
    CostMulDistrib(iters, 1, iters + 1, 7 * n + 5);
    iters := iters + 1;
    if cnt == 1 {
      break;
    }
    steps := steps + 1;
    mask := mask / 2;
  }
  assert {:split_here} true;
  CostMulMonoLeft(iters, 31, 7 * n + 5);
  steps := steps + 1;
  steps := steps + 1;
  var i := n - 1;
  var found := false;
  var idx := 0;
  ghost var b2 := steps;
  while idx < n && !found
    invariant 0 <= idx <= n
    invariant 0 <= i < n
    invariant |a| == n
    invariant 0 <= mask <= 1073741824
    invariant forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 1073741824
    invariant steps <= b2 + 8 * idx
    decreases n - idx
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
  assert {:split_here} true;
  steps := steps + (2 + if idx < n then 1 else 0);
  steps := steps + 1;
  var tmp := a[0];
  assert 0 <= i < |a|;
  steps := steps + 3;
  a := a[0 := a[i]][i := tmp];
  steps := steps + n;
  assert {:split_here} true;
  var parts := seq(n, _ /* _v0 */ => "");
  var p := 0;
  ghost var d: nat := 0;
  ghost var b3 := steps;
  while p < n
    invariant 0 <= p <= n
    invariant |parts| == n
    invariant |a| == n
    invariant SumLen(parts[..p]) == d
    invariant steps <= b3 + 5 * p + d
    decreases n - p
  {
    ghost var s := IntToString(a[p]);
    IntToStringDigits(a[p]);
    ghost var oldparts := parts;
    steps := steps + 2;
    steps := steps + (2 + Digits(a[p]));
    parts := parts[p := IntToString(a[p])];
    assert parts[..p] == oldparts[..p];
    assert parts[..p + 1] == oldparts[..p] + [s];
    SumLenSnoc(oldparts[..p], s);
    d := d + |s|;
    steps := steps + 1;
    p := p + 1;
  }
  assert parts[..n] == parts;
  JoinLen(parts, " ");
  steps := steps + 1;
  steps := steps + (SumLen(parts) + |parts| + |"\n"|);
  output := Join(parts, " ") + "\n";
}

import opened Prelude
