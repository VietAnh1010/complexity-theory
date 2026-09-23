// 450_A. Jzzhu and Children  (problem 2992, solution 2992_153)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n = input().split()
// a = int(n[0])
// b = int(n[1])
// c = []
// t = input().split()
// for i in range(a):
//     c.append([int(t[i]),0,int(i)])
//     c[i][1] = math.ceil(c[i][0] / b)
// c.sort(key = lambda x:(x[1],x[2]))
// print(c[-1][2]+1)
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

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |a_list| * (CeilLog2(|a_list|) + 1) + 5 * |a_list| + 8
{
  var c: seq<(int, int, int)> := [];
  var i := 0;
  steps := 1;
  ghost var base1 := steps;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant |c| == i
    invariant steps == base1 + 3 * i
    decreases |a_list| - i
  {
    var v := a_list[i];
    var ceilVal := if k != 0 then (v + k - 1) / k else 0;
    c := c + [(v, ceilVal, i)];
    i := i + 1;
    steps := steps + 3;
  }
  SortCostTreeBound(|c|);
  steps := steps + SortCost(|c|);
  var sorted := Sort(c, (x: (int, int, int), y: (int, int, int)) =>
    x.1 < y.1 || (x.1 == y.1 && x.2 < y.2));
  SortLength(c, (x: (int, int, int), y: (int, int, int)) =>
    x.1 < y.1 || (x.1 == y.1 && x.2 < y.2));
  if |sorted| > 0 {
    output := IntToString(sorted[|sorted| - 1].2 + 1);
  } else {
    output := IntToString(0);
  }
  steps := steps + 2;
}
