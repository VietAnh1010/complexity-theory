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

method Solve(n: int, m: int, values: seq<int>) returns (output: string)
  requires forall x :: x in values ==> 1 <= x <= 100
{
  var asc := SortInts(values);
  SortElems(values, (x, y) => x < y);
  assert forall x :: x in asc ==> x in values;
  var result := 0;
  var found := false;
  var i := |asc| - 1;
  while i >= 0 && !found
    invariant -1 <= i < |asc|
    decreases i + 1
  {
    assert asc[i] in asc;
    if FloorMod(m, asc[i]) == 0 {
      result := FloorDiv(m, asc[i]);
      found := true;
    }
    i := i - 1;
  }
  output := IntToString(result);
}
