// 1197_B. Pillars  (problem 1453, solution 1453_211)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def f(l):
//     for i in range(len(l)-1):
//         if l[i] > l[i+1]:
//             break
//     #print(i+1)
//     if sorted(l[i+1:],reverse=True) == l[i+1:]:return 0
//     return 1
// 
// M = 10**9 + 7
// R = lambda: map(int, input().split())
// n = int(input())
// L = list(R())
// if len(set(L)) != n:print("NO")
// else:print("YNEOS"[f(L)::2])
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

// Sort/Merge are plain recursive functions in prelude.dfy (off limits, so no
// ghost step counter can be attached there). Their cost is charged as an
// opaque-but-defined function SortCost, whose recursion mirrors Sort's own
// split. SortCostBound proves a quadratic bound on it -- looser than the
// true O(k log k), which is the tight bound proved elsewhere in this corpus
// (solutions-proved/nlogn/) via a CeilLog2 recursion-tree argument. Given the
// per-row attempt/time budget, this copy keeps the simpler quadratic
// scaffold: relation looser-slack.
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
    assert SortCost(k) == SortCost(L) + SortCost(R) + k;
    assert SortCost(L) + SortCost(R) + k <= (2 * L * L + 1) + (2 * R * R + 1) + k;
    assert (2 * L * L + 1) + (2 * R * R + 1) + k == 2 * L * L + 2 * R * R + k + 2;
    assert 2 * L * L + 2 * R * R + k + 2 <= (k * k + 1) + k + 2;
    QuadTail(k);
  }
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  ensures steps <= 2 * n * n + 10 * n + 10
{
  var nn := if n >= 0 then n else 0;
  SortLength(a_list, (x: int, y: int) => x < y);
  SortCostBound(nn);
  var sortedL := SortInts(a_list);
  steps := 1 + SortCost(nn);
  var hasDup := false;
  var j := 0;
  while j < |sortedL| - 1
    invariant 0 <= j <= |sortedL|
    invariant steps <= 1 + SortCost(nn) + 2 * j
    decreases |sortedL| - 1 - j
  {
    if sortedL[j] == sortedL[j+1] { hasDup := true; }
    j := j + 1;
    steps := steps + 2;
  }
  if hasDup {
    output := "NO";
  } else {
    var i := 0;
    ghost var base2 := steps;
    while i < n - 2 && !(a_list[i] > a_list[i+1])
      invariant 0 <= i <= n
      invariant steps <= base2 + 2 * i
      decreases n - 2 - i
    {
      i := i + 1;
      steps := steps + 2;
    }
    var nonInc := true;
    var p := i + 1;
    ghost var base3 := steps;
    while p < n - 1
      invariant 0 <= p <= n + 1
      invariant steps <= base3 + 2 * (p - i - 1)
      decreases n - 1 - p
    {
      if a_list[p] < a_list[p+1] { nonInc := false; }
      p := p + 1;
      steps := steps + 2;
    }
    output := if nonInc then "YES" else "NO";
    steps := steps + 1;
  }
}
