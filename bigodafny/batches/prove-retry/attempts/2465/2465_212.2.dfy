// 1299_A. Anu Has a Function  (problem 2465, solution 2465_212)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
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

include "../../prelude.dfy"
import opened Prelude

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

method Solve(t: int, n_list: seq<int>) returns (output: string, ghost steps: nat)
  requires t >= 1
  requires |n_list| == t
  requires forall v :: v in n_list ==> 0 <= v < 0x40000000
  ensures steps <= 2 * NLogN(t) + 170 * t + 2 * |output| + 200
{
  steps := 1;
  var n := t;
  var a := Sort(n_list, (x: int, y: int) => x > y);
  steps := steps + SortCost(n);
  SortCostWithin(n, n);
  SortElems(n_list, (x: int, y: int) => x > y);
  assert |a| == n by { SortIsPermutation(n_list, (x: int, y: int) => x > y); }
  assert forall v :: v in a ==> 0 <= v < 0x40000000;
  assert forall idx2 :: 0 <= idx2 < |a| ==> a[idx2] in a;
  assert forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 0x40000000;
  var mask := 0x40000000;
  Lg30();
  ghost var iters: nat := 0;
  ghost var b0 := steps;
  while mask != 0
    invariant 0 <= mask <= 0x40000000
    invariant |a| == n
    invariant forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 0x40000000
    invariant iters + Lg(mask) <= 31
    invariant steps <= b0 + iters * (5 * n + 5)
    decreases mask
  {
    var cnt := 0;
    var k := 0;
    ghost var b1 := steps;
    while k < n
      invariant 0 <= k <= n
      invariant 0 <= mask <= 0x40000000
      invariant |a| == n
      invariant forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 0x40000000
      invariant steps == b1 + 5 * k
      decreases n - k
    {
      if BitAnd(a[k], mask) != 0 {
        cnt := cnt + 1;
      }
      k := k + 1;
      steps := steps + 5;
    }
    steps := steps + 5;
    CostMulDistrib(iters, 1, iters + 1, 5 * n + 5);
    iters := iters + 1;
    if cnt == 1 {
      break;
    }
    mask := mask / 2;
  }
  CostMulMonoLeft(iters, 31, 5 * n + 5);
  assert steps <= b0 + 31 * (5 * n + 5);
  var i := n - 1;
  var found := false;
  var idx := 0;
  ghost var b2 := steps;
  while idx < n && !found
    invariant 0 <= idx <= n
    invariant 0 <= i < n
    invariant |a| == n
    invariant 0 <= mask <= 0x40000000
    invariant forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 0x40000000
    invariant steps == b2 + 5 * idx
    decreases n - idx
  {
    if BitAnd(a[idx], mask) != 0 {
      i := idx;
      found := true;
    }
    idx := idx + 1;
    steps := steps + 5;
  }
  var tmp := a[0];
  assert 0 <= i < |a|;
  a := a[0 := a[i]][i := tmp];
  steps := steps + 5;
  var parts := seq(n, _ => "");
  steps := steps + 1;
  var p := 0;
  ghost var d: nat := 0;
  ghost var b3 := steps;
  while p < n
    invariant 0 <= p <= n
    invariant |parts| == n
    invariant |a| == n
    invariant SumLen(parts[..p]) == d
    invariant steps == b3 + 4 * p + d
    decreases n - p
  {
    var s := IntToString(a[p]);
    IntToStringDigits(a[p]);
    assert parts[..p + 1] == parts[..p] + [s] by {
      assert parts[p := s][..p] == parts[..p];
    }
    parts := parts[p := s];
    SumLenSnoc(parts[..p], s);
    d := d + |s|;
    steps := steps + 4 + |s|;
    p := p + 1;
  }
  assert parts[..n] == parts;
  JoinLen(parts, " ");
  output := Join(parts, " ") + "\n";
  steps := steps + SumLen(parts) + n + 2;
}
