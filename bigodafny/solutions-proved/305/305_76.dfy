// 350_A. TL  (problem 305, solution 305_76)
// time complexity: O(nlogn+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m = map(int, input().split())
// a = list(map(int, input().split()))
// b = list(map(int, input().split()))
// a.sort()
// b.sort()
// am = a[0]
// bm = min(b)
// i = b[0] - 1
// while i >= 2*am and a[-1] <= i and i > 0:
//     i -= 1
// i+=1
// if i == 0 or not(i >= 2*am and a[-1] <= i and i > 0) or bm <= i:
//     print(-1)
// else:
//     print(i)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MergeLength<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
  ensures |Merge(a, b, less)| == |a| + |b|
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
  } else if less(b[0], a[0]) {
    MergeLength(a, b[1..], less);
  } else {
    MergeLength(a[1..], b, less);
  }
}

lemma SortLength<T>(s: seq<T>, less: (T, T) -> bool)
  ensures |Sort(s, less)| == |s|
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortLength(s[..|s| / 2], less);
    SortLength(s[|s| / 2..], less);
    MergeLength(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
  }
}

// Same quadratic scaffold as elsewhere in this corpus (e.g.
// solutions-proved/2593/2593_332.dfy): Sort/Merge live in prelude.dfy and
// cannot carry a ghost step counter, so their cost is charged through an
// opaque SortCost whose recursion mirrors the split, bounded quadratically
// rather than by the tight O(k log k) CeilLog2 argument. relation:
// looser-slack.
ghost function SortCost(k: nat): nat
  decreases k
{
  if k <= 1 then 1
  else SortCost(k / 2) + SortCost(k - k / 2) + k
}

lemma SquareSplit(k: nat, L: nat)
  requires 2 * L <= k <= 2 * L + 1
  ensures 2 * L * L + 2 * (k - L) * (k - L) <= k * k + 1
{
  var d := k - 2 * L;
  assert d == 0 || d == 1;
  assert k - L == L + d;
  assert 2 * L * L + 2 * (k - L) * (k - L) == 4 * L * L + 4 * L * d + 2 * d * d;
  assert k == 2 * L + d;
  assert k * k == 4 * L * L + 4 * L * d + d * d;
  assert d * d <= 1;
}

lemma QuadTail(k: nat)
  requires k >= 2
  ensures k * k + k + 3 <= 2 * k * k + 1
{
  assert (k - 2) * (k + 1) >= 0;
}

lemma SortCostBound(k: nat)
  ensures SortCost(k) <= 2 * k * k + 1
  decreases k
{
  if k <= 1 {
  } else {
    var L := k / 2;
    var R := k - L;
    SortCostBound(L);
    SortCostBound(R);
    SquareSplit(k, L);
    assert SortCost(k) == SortCost(L) + SortCost(R) + k;
    assert SortCost(L) + SortCost(R) + k <= (2 * L * L + 1) + (2 * R * R + 1) + k;
    assert (2 * L * L + 1) + (2 * R * R + 1) + k == 2 * L * L + 2 * R * R + k + 2;
    assert 2 * L * L + 2 * R * R + k + 2 <= (k * k + 1) + k + 2;
    QuadTail(k);
  }
}

// The while loop below decreases from `d_list`'s minimum value down toward
// `2*am`, one unit at a time. Its iteration count is bounded by that VALUE
// gap, not by |c_list|/|d_list| -- a cost the O(nlogn+mlogm) label (fit by
// profiling on bounded test values) omits entirely. Per the value-vs-size
// convention this value is written into the bound as its own parameter.
// relation: looser-structural.
method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |c_list| >= 1 && |d_list| >= 1
  ensures steps <= 2 * |c_list| * |c_list| + 2 * |d_list| * |d_list| + 4 * |c_list| + 4 * |d_list|
                   + 2 * (if SortInts(d_list)[0] - 1 > 0 then SortInts(d_list)[0] - 1 else 0) + 20
{
  var na := |c_list|;
  var nb := |d_list|;
  SortLength(c_list, (x: int, y: int) => x < y);
  SortLength(d_list, (x: int, y: int) => x < y);
  SortCostBound(na);
  SortCostBound(nb);
  var aSorted := SortInts(c_list);
  var bSorted := SortInts(d_list);
  steps := 1 + SortCost(na) + SortCost(nb);
  var am := aSorted[0];
  var bm := bSorted[0];
  var amax := aSorted[|aSorted| - 1];
  var i := bSorted[0] - 1;
  ghost var base1 := steps;
  ghost var i0 := i;
  ghost var i0cap := if i0 > 0 then i0 else 0;
  while i >= 2 * am && amax <= i && i > 0
    invariant i <= i0
    invariant 0 <= i0 - i <= i0cap
    invariant steps <= base1 + 2 * (i0 - i)
    decreases i
  {
    i := i - 1;
    steps := steps + 2;
  }
  i := i + 1;
  steps := steps + 1;
  if i == 0 || !(i >= 2 * am && amax <= i && i > 0) || bm <= i {
    output := "-1";
  } else {
    output := IntToString(i);
  }
  steps := steps + 2;
}
