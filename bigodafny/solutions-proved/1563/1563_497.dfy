// 915_A. Garden  (problem 1563, solution 1563_497)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// buckets, length = map(int,input().split())
// data = list(map(int,input().split()))
// data.sort(reverse=True)
// for element in data:
//     if length % element == 0:
//         print(length // element)
//         break
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

// Sort's own cost via the standard T(k) = T(k/2) + T(k-k/2) + k recurrence,
// bounded O(k log k) -- precedent solutions-proved/1871/1871_156.dfy. The
// scan loop is linear and dominated, so the whole method is O(k log k).

method Solve(n: int, m: int, values: seq<int>) returns (output: string, ghost steps: nat)
  // Python evaluates m % v for the same v; a zero raises ZeroDivisionError.
  requires forall k :: 0 <= k < |values| ==> values[k] != 0
  ensures steps <= 2 * |values| * (CeilLog2(|values|) + 1) + 5 * |values| + |output| + 10
{
  var asc := SortInts(values);
  SortElems(values, (x, y) => x < y);
  SortCostTreeBound(|values|);
  steps := 1 + SortCost(|values|);
  assert forall x :: x in asc ==> x in values;
  assert |asc| == |values|;
  var result := 0;
  var found := false;
  var i := |asc| - 1;
  ghost var cnt := 0;
  ghost var base1 := steps;
  while i >= 0 && !found
    invariant -1 <= i < |asc|
    invariant cnt == (|asc| - 1) - i
    invariant steps <= base1 + 3 * cnt
    decreases i + 1
  {
    assert asc[i] in asc;
    if FloorMod(m, asc[i]) == 0 {
      result := FloorDiv(m, asc[i]);
      found := true;
    }
    i := i - 1;
    cnt := cnt + 1;
    steps := steps + 3;
  }
  assert cnt <= |asc|;
  assert steps <= base1 + 3 * |asc|;
  output := IntToString(result);
  steps := steps + |output| + 2;
}
