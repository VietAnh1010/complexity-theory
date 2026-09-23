// 999_C. Alphabetic Removals  (problem 2725, solution 2725_319)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=list(map(int,input().split()))
// s=list(input())
// x=sorted([j,i] for i,j in enumerate(s))
// #print(x)
// for i in range(k):
//     s[x[i][1]]=''
// print(''.join(s))
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

method Solve(n: int, k: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|s|) + 1 + 11 * |s| + 8
{
  steps := 1;
  var pairArr: seq<(char, int)> := seq(|s|, _ => (' ', 0));
  var i := 0;
  steps := steps + 1;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |pairArr| == |s|
    invariant steps <= 3 * i + 2
    decreases |s| - i
  {
    pairArr := pairArr[i := (s[i], i)];
    i := i + 1;
    steps := steps + 3;
  }
  var pairs := pairArr;
  steps := steps + 1;
  SortCostNLogN(|s|);
  var sorted := Sort(pairs, (x: (char, int), y: (char, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  SortLength(pairs, (x: (char, int), y: (char, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  steps := steps + SortCost(|s|);
  var removed := seq(|s|, _ => false);
  var z := 0;
  steps := steps + 1;
  while z < |s|
    invariant 0 <= z <= |s|
    invariant |removed| == |s|
    invariant steps <= 2 * z + SortCost(|s|) + 3 * |s| + 4
    decreases |s| - z
  {
    removed := removed[z := false];
    z := z + 1;
    steps := steps + 2;
  }
  var j := 0;
  steps := steps + 1;
  while j < k && j < |sorted|
    invariant 0 <= j <= |sorted|
    invariant |removed| == |s|
    invariant steps <= 3 * j + SortCost(|s|) + 2 * |s| + 3 * |s| + 5
    decreases |sorted| - j
  {
    var target := sorted[j].1;
    if 0 <= target < |s| {
      removed := removed[target := true];
    }
    j := j + 1;
    steps := steps + 3;
  }
  var buf := seq(|s|, _ => ' ');
  var w := 0;
  var m := 0;
  steps := steps + 1;
  while m < |s|
    invariant 0 <= m <= |s|
    invariant 0 <= w <= m
    invariant |buf| == |s| && |removed| == |s|
    invariant steps <= 3 * m + SortCost(|s|) + 5 * |s| + 3 * |s| + 6
    decreases |s| - m
  {
    if !removed[m] {
      buf := buf[w := s[m]];
      w := w + 1;
    }
    m := m + 1;
    steps := steps + 3;
  }
  output := buf[0..w];
  steps := steps + 1;
}
