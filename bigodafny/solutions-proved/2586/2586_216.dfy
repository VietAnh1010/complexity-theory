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

// Sort/merge cost scaffold, standard across the nlogn rows (precedent:
// solutions-proved/1871/1871_156.dfy).
ghost function SortCost(k: nat): nat
  decreases k
{
  if k <= 1 then 1
  else SortCost(k / 2) + SortCost(k - k / 2) + k
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
  SortCostNLogN(|a_list|);
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
