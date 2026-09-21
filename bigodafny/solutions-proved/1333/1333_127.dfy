// 1029_C. Maximal Intersection  (problem 1333, solution 1333_127)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// L = []
// R = []
// S = []
// for _ in range(n):
//     a,b = [int(x) for x in input().split()]
//     L.append(a)
//     R.append(b)
//     S.append((a,b))
//
//
// L.sort(reverse = True)
// R.sort()
//
// if (L[0],R[0]) in S:
//     print(max(R[1]-L[1],0))
// else:
//     print(max(R[0]-L[1],R[1]-L[0],0))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
// Prelude.Sort is a plain recursive function (merge sort); it carries no
// ghost step counter (prelude.dfy is off limits), so its cost is charged as
// an opaque-but-defined SortCost mirroring Sort's own split. The bound proved
// here is an honest O(k^2) -- weaker than merge sort's true O(k log k) --
// so relation = looser-slack.
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

method Solve(n: int, intervals: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n >= 2
  requires n == |intervals|
  requires forall k :: 0 <= k < n ==> |intervals[k]| >= 2
  ensures steps <= 2 * SortCost(n) + 5 * n + 10
{
{

  steps := 1;
  var L := seq(n, idx requires 0 <= idx < n => intervals[idx][0]);
  var R := seq(n, idx requires 0 <= idx < n => intervals[idx][1]);
  steps := steps + 2 * n;
  SortCostBound(n);
  var Ldesc := Sort(L, (x: int, y: int) => x > y);
  SortLength(L, (x, y) => x > y);
  steps := steps + SortCost(n);
  var Rasc := SortInts(R);
  SortLength(R, (x, y) => x < y);
  steps := steps + SortCost(n);
  var found := false;
  var idx2 := 0;
  while idx2 < n
    invariant 0 <= idx2 <= n
    invariant steps <= 3 * idx2 + 2 * n + 2 * SortCost(n) + 1
    decreases n - idx2
  {
    if intervals[idx2][0] == Ldesc[0] && intervals[idx2][1] == Rasc[0] {
      found := true;
    }
    idx2 := idx2 + 1;
    steps := steps + 3;
  }
  var ans := 0;
  if found {
    var v := Rasc[1] - Ldesc[1];
    ans := if v > 0 then v else 0;
  } else {
    var v1 := Rasc[0] - Ldesc[1];
    var v2 := Rasc[1] - Ldesc[0];
    var mx := if v1 > v2 then v1 else v2;
    ans := if mx > 0 then mx else 0;
  }
  steps := steps + 3;
  output := IntToString(ans);
  steps := steps + 1;
}
}
