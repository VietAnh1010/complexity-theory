// 546_B. Soldier and Badges  (problem 2586, solution 2586_216)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// ans=0
// s=sorted(list(map(int,input().split())))
// for i in range(1,n):
//     if s[i]<=s[i-1]:
//         ans+=s[i-1]-s[i]+1
//         s[i]=s[i-1]+1
// print(ans)
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

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

lemma NMonoBound(i: int, m: int, K: int)
  requires 1 <= i <= m
  requires K >= 0
  ensures K * (i - 1) <= K * m
{
  MulMonoRight(K, i - 1, m);
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n >= 1
  ensures steps <= 2 * |a_list| * (CeilLog2(|a_list|) + 1) + 6 * |a_list| + 12
{
  SortLength(a_list, (x: int, y: int) => x < y);
  var s := SortInts(a_list);
  SortCostTreeBound(|a_list|);
  steps := 1 + SortCost(|a_list|);
  var ans := 0;
  var i := 1;
  ghost var base1 := steps;
  while i < n
    invariant 1 <= i <= n
    invariant |s| == n
    invariant steps == base1 + 4 * (i - 1)
    decreases n - i
  {
    if s[i] <= s[i - 1] {
      ans := ans + s[i - 1] - s[i] + 1;
      s := s[i := s[i - 1] + 1];
    }
    i := i + 1;
    steps := steps + 4;
  }
  output := IntToString(ans);
  steps := steps + 1;
  NMonoBound(i, n, 4);
  assert steps <= base1 + 4 * n + 1;
}
