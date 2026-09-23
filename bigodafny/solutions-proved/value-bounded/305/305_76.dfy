// VALUE-BOUNDED -- filed for review; the proof carries a term the label omits.
//
//   This proof's bound depends on the MAGNITUDE of an input, not only on how
//   many inputs there are. BigOBench fitted the label by profiling, which
//   treats a capped value as constant; COMPLEXITY.md section 1 decides the
//   opposite, so the two disagree here by construction.
//
//   See solutions-proved/value-bounded/README.md for the category and
//   MANIFEST.jsonl for this row's entry.
//
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

//   Bound replaced 2026-09-22. prove-sample-5 redrew this row (a sampler bug
//   of mine let value-bounded/ rows back into the pool) and produced a
//   STRICTLY BETTER proof: the tight CeilLog2 recursion tree for both sorts
//   instead of the quadratic SortCost scaffold, with the value term isolated
//   as 4 * AbsInt(SortInts(d_list)[0]). The nlogn+mlogm half of the label is
//   now confirmed outright and only the value term is left over, which is
//   exactly what a looser-structural row should look like.
//
include "../../../prelude.dfy"
import opened Prelude

// VALUE-BOUNDED: the while loop's iteration count is bounded by the input
// VALUE SortInts(d_list)[0] (roughly d_list's minimum), not by n or m. Per
// the value-vs-size convention that value is charged as its own parameter,
// via AbsInt(SortInts(d_list)[0]) below -- a real cost the O(nlogn+mlogm)
// label omits (relation: looser-structural).
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

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |c_list| >= 1 && |d_list| >= 1
  ensures steps <= 2 * |c_list| * (CeilLog2(|c_list|) + 1)
                  + 2 * |d_list| * (CeilLog2(|d_list|) + 1)
                  + 4 * AbsInt(SortInts(d_list)[0]) + 20
{
  SortCostTreeBound(|c_list|);
  SortCostTreeBound(|d_list|);
  steps := 1 + SortCost(|c_list|) + SortCost(|d_list|);
  var aSorted := SortInts(c_list);
  var bSorted := SortInts(d_list);
  SortLength(c_list, (x: int, y: int) => x < y);
  SortLength(d_list, (x: int, y: int) => x < y);
  var am := aSorted[0];
  var bm := bSorted[0];
  var amax := aSorted[|aSorted| - 1];
  var i := bSorted[0] - 1;
  ghost var iInit := i;
  steps := steps + 4;
  ghost var base1 := steps;
  while i >= 2 * am && amax <= i && i > 0
    invariant i <= iInit
    invariant i >= 0 || i == iInit
    invariant steps == base1 + 4 * (iInit - i)
    decreases i
  {
    i := i - 1;
    steps := steps + 4;
  }
  assert iInit - i <= AbsInt(iInit);
  assert AbsInt(iInit) <= AbsInt(bSorted[0]) + 1;
  i := i + 1;
  steps := steps + 1;
  if i == 0 || !(i >= 2 * am && amax <= i && i > 0) || bm <= i {
    output := "-1";
  } else {
    output := IntToString(i);
  }
  steps := steps + 2;
}
