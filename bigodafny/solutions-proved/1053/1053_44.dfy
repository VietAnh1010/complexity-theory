// 605_A. Sorting Railway Cars  (problem 1053, solution 1053_44)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// p=list(map(int,input().split()))
// for i in range(n):
//     p[i]=[p[i],i]
// p.sort()
// b=1
// d=[]
// for i in range(n-1):
//     if p[i][1]<p[i+1][1]:
//         b+=1
//     else:
//         d.append(b)
//         b=1
// d.append(b)
// print(n-max(d))
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

method Solve(N: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| == N
  ensures steps <= 2 * |a_list| * (CeilLog2(|a_list|) + 1) + 5 * |a_list| + 12
{
  var pairs := seq(|a_list|, i requires 0 <= i < |a_list| => (a_list[i], i));
  SortCostTreeBound(|pairs|);
  steps := 1 + |a_list| + SortCost(|pairs|);
  var sortedPairs := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  SortLength(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  var idxSeq := seq(|sortedPairs|, i requires 0 <= i < |sortedPairs| => sortedPairs[i].1);
  steps := steps + |a_list|;
  var b := 1;
  var maxD := 0;
  var i := 0;
  ghost var base1 := steps;
  while i < N - 1
    invariant 0 <= i <= N
    invariant |idxSeq| == N
    invariant steps == base1 + 3 * i
    decreases N - 1 - i
  {
    if idxSeq[i] < idxSeq[i + 1] {
      b := b + 1;
    } else {
      if b > maxD { maxD := b; }
      b := 1;
    }
    i := i + 1;
    steps := steps + 3;
  }
  if b > maxD { maxD := b; }
  output := IntToString(N - maxD);
  steps := steps + 1;
}
