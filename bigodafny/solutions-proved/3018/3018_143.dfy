// 299_A. Ksusha and Array  (problem 3018, solution 3018_143)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
//
// a.sort()
//
// t = a[0]
// for x in a:
//     if x % a[0] != 0:
//         t = -1
//
// print(t)
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

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |a_list| * (CeilLog2(|a_list|) + 1) + 4 * |a_list| + 12
{
  steps := 1;
  if |a_list| == 0 {
    output := "";
    steps := steps + 1;
    return;
  }
  SortLength(a_list, (x: int, y: int) => x < y);
  var a := SortInts(a_list);
  SortCostTreeBound(|a_list|);
  steps := steps + SortCost(|a_list|);
  var m := a[0];
  var t := m;
  var i := 0;
  ghost var base1 := steps;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |a| == |a_list|
    invariant steps == base1 + 3 * i
    decreases |a| - i
  {
    if m != 0 && FloorMod(a[i], m) != 0 {
      t := -1;
    }
    i := i + 1;
    steps := steps + 3;
  }
  output := IntToString(t);
  steps := steps + 1;
}
