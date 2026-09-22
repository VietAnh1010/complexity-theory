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
    QuadTail(k);
  }
}

ghost function CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }

lemma CeilLog2Monotone(m: nat, n: nat)
  requires m <= n
  ensures CeilLog2(m) <= CeilLog2(n)
  decreases n
{
  if n <= 1 { }
  else if m <= 1 { }
  else { CeilLog2Monotone((m + 1) / 2, (n + 1) / 2); }
}

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

lemma MulDistrib(a: nat, b: nat, k: nat, L: nat)
  requires a + b == k
  ensures a * L + b * L == k * L
{ }

lemma SortCostNLogN(k: nat)
  ensures SortCost(k) <= 2 * k * (CeilLog2(k) + 1) + 1
  decreases k
{
  if k <= 1 { return; }
  var a := k / 2;
  var b := k - k / 2;
  var L := CeilLog2(k);
  assert a + b == k;
  assert b == (k + 1) / 2;
  assert a <= b;
  SortCostNLogN(a);
  SortCostNLogN(b);
  CeilLog2Monotone(a, b);
  assert L == 1 + CeilLog2(b);
  assert CeilLog2(a) + 1 <= L;
  assert CeilLog2(b) + 1 == L;
  MulMonoRight(2 * a, CeilLog2(a) + 1, L);
  MulMonoRight(2 * b, CeilLog2(b) + 1, L);
  assert SortCost(a) <= 2 * a * L + 1;
  assert SortCost(b) <= 2 * b * L + 1;
  MulDistrib(2 * a, 2 * b, 2 * k, L);
  assert 2 * a * L + 2 * b * L == 2 * k * L;
  assert SortCost(k) == SortCost(a) + SortCost(b) + k;
  assert SortCost(k) <= 2 * k * L + k + 2;
  assert 2 * k * (L + 1) == 2 * k * L + 2 * k;
  assert k + 2 <= 2 * k + 1;
}

method Solve(n: int, pairs: seq<(int, int)>) returns (output: string, ghost steps: nat)
  requires |pairs| == n
  requires n >= 1
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 10 * n + 10
{
  SortCostNLogN(n);
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
