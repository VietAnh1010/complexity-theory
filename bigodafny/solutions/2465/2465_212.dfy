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

method Solve(t: int, n_list: seq<int>) returns (output: string)
  requires t >= 1
  requires |n_list| == t
  requires forall v :: v in n_list ==> 0 <= v < 0x40000000
{
  var n := t;
  var a := Sort(n_list, (x: int, y: int) => x > y);
  SortElems(n_list, (x: int, y: int) => x > y);
  assert |a| == n;
  assert forall v :: v in a ==> 0 <= v < 0x40000000;
  assert forall idx2 :: 0 <= idx2 < |a| ==> a[idx2] in a;
  assert forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 0x40000000;
  var mask := 0x40000000;
  while mask != 0
    invariant 0 <= mask <= 0x40000000
    invariant |a| == n
    invariant forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 0x40000000
    decreases mask
  {
    var cnt := 0;
    var k := 0;
    while k < n
      invariant 0 <= k <= n
      invariant 0 <= mask <= 0x40000000
      invariant |a| == n
      invariant forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 0x40000000
    {
      if BitAnd(a[k], mask) != 0 {
        cnt := cnt + 1;
      }
      k := k + 1;
    }
    if cnt == 1 {
      break;
    }
    mask := mask / 2;
  }
  var i := n - 1;
  var found := false;
  var idx := 0;
  while idx < n && !found
    invariant 0 <= idx <= n
    invariant 0 <= i < n
    invariant |a| == n
    invariant 0 <= mask <= 0x40000000
    invariant forall idx2 :: 0 <= idx2 < |a| ==> 0 <= a[idx2] < 0x40000000
  {
    if BitAnd(a[idx], mask) != 0 {
      i := idx;
      found := true;
    }
    idx := idx + 1;
  }
  var tmp := a[0];
  assert 0 <= i < |a|;
  a := a[0 := a[i]][i := tmp];
  var parts := new string[n];
  var p := 0;
  while p < n
    invariant 0 <= p <= n
  {
    parts[p] := IntToString(a[p]);
    p := p + 1;
  }
  output := Join(parts[..], " ") + "\n";
}
