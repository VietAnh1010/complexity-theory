// p02899 AtCoder Beginner Contest 142 - Go to School  (problem 1421, solution 1421_89)
// time complexity: O(nlogn)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = map(int, input().split())
//
// for i, x in sorted(enumerate(a), key=lambda x:x[1]):
// 	print(i+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
// Same SortCost scaffold as elsewhere: an honest O(k^2) bound on Sort,
// weaker than merge sort's true O(k log k).
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

lemma SortLen<T>(s: seq<T>, less: (T, T) -> bool)
  ensures |Sort(s, less)| == |s|
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortLen(s[..|s| / 2], less);
    SortLen(s[|s| / 2..], less);
    MergeLength(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
  }
}

// Label O(nlogn) -- disagrees with the proof below, which only establishes
// O(n^2): SortCost's honest bound (the tight recursion-tree argument for
// merge sort's O(n log n) is not attempted here). The pairs/output builders
// are O(n); JoinInts is charged a flat O(1) per element (IntToString's
// digit-count growth is not the point of this row and is not tracked).
method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |a_list| * |a_list| + 6 * |a_list| + 5
{
  var pairs := seq(|a_list|, i requires 0 <= i < |a_list| => (a_list[i], i));
  SortCostBound(|pairs|);
  steps := 1 + |a_list| + SortCost(|pairs|);
  var srt := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  SortLen(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  assert |srt| == |a_list|;
  var vals := seq(|srt|, i requires 0 <= i < |srt| => srt[i].1 + 1);
  steps := steps + |a_list|;
  if |vals| == 0 {
    output := "";
  } else {
    output := JoinInts(vals, "\n") + "\n";
    steps := steps + 2 * |vals|;
  }
}
