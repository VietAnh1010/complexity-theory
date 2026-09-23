// 545_C. Woodcutters  (problem 1560, solution 1560_63)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// inf = 10**18
// a=[]
// n = int(input())
// for i in range(n):
//     a.append([int(i) for i in input().split()])
// a.sort()
// occ = [a[0][0]-a[0][1],a[0][0]]
// ans=1
// for j in range(1,n):
//     i=a[j][:]
//     cur1=[i[0]-i[1],i[0]]
//     cur2=[i[0],i[0]+i[1]]
//     if occ[1]<cur1[0]:
//         occ[1]=cur1[1]
//         ans+=1
//     elif occ[1]<cur2[0] and (j+1==n or(j+1<n and cur2[1]<a[j+1][0])):
//         occ[1]=cur2[1]
//         ans+=1
//     else:
//         occ[1]=i[0]
// print(ans)
//
//
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
// Same SortCost/CeilLog2 recursion-tree argument as
// solutions-proved/nlogn/1484/1484_82.dfy: Sort carries no ghost step
// counter of its own, so its cost is charged as an opaque-but-defined
// SortCost mirroring Sort's own split.

method Solve(n: int, pairs: seq<(int, int)>) returns (output: string, ghost steps: nat)
  requires |pairs| == n
  requires n >= 1
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 10 * n + 10
{
  SortCostTreeBound(n);
  steps := 1 + SortCost(n);
  var a := Sort(pairs, (p: (int, int), q: (int, int)) => p.0 < q.0 || (p.0 == q.0 && p.1 < q.1));
  SortLen1560(pairs, (p: (int, int), q: (int, int)) => p.0 < q.0 || (p.0 == q.0 && p.1 < q.1));
  var occ1 := a[0].0;
  var ans := 1;
  var j := 1;
  ghost var b2 := steps;
  while j < n
    invariant 1 <= j <= n
    invariant |a| == n
    invariant steps <= b2 + 8 * (j - 1)
    decreases n - j
  {
    var xi := a[j].0;
    var hi := a[j].1;
    var cur1_0 := xi - hi;
    var cur1_1 := xi;
    var cur2_0 := xi;
    var cur2_1 := xi + hi;
    if occ1 < cur1_0 {
      occ1 := cur1_1;
      ans := ans + 1;
    } else if occ1 < cur2_0 && (j+1 == n || (j+1 < n && cur2_1 < a[j+1].0)) {
      occ1 := cur2_1;
      ans := ans + 1;
    } else {
      occ1 := xi;
    }
    j := j + 1;
    steps := steps + 8;
  }
  output := IntToString(ans);
  steps := steps + 1;
}

lemma MergeLen1560<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
  ensures |Merge(a, b, less)| == |a| + |b|
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
  } else if less(b[0], a[0]) {
    MergeLen1560(a, b[1..], less);
  } else {
    MergeLen1560(a[1..], b, less);
  }
}

lemma SortLen1560<T>(s: seq<T>, less: (T, T) -> bool)
  ensures |Sort(s, less)| == |s|
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortLen1560(s[..|s| / 2], less);
    SortLen1560(s[|s| / 2..], less);
    MergeLen1560(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
  }
}
