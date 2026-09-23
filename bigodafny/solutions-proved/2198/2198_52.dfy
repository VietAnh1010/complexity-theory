// 788_A. Functions again  (problem 2198, solution 2198_52)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
//
// b = []
// for i in range(n - 1):
//     b.append(abs(a[i] - a[i + 1]))
//
// c = []
// s = 1
// summ = 0
// for i in range(n - 1):
//     summ += s * b[i]
//     s = -s
//     c.append(summ)
//
// c.sort()
//
// if c[0] < 0:
//     print(c[n - 2] - c[0])
// else:
//     print(c[n - 2])
// --------------------------------------------------------------------
//
// PROOF NOTE (relation: looser-slack). SortInts(c) costs SortCost(n-1),
// bounded here by the corpus's standard O(k^2) scaffold rather than the
// tight O(k log k) merge-sort argument, so the proved bound is O(n^2), not
// the tight O(n log n).

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
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
  requires n >= 2
  requires n <= |a_list|
  ensures steps <= SortCost(n - 1) + 8 * n + 10
{
  var b: seq<int> := [];
  var i := 0;
  steps := 3;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant |b| == i
    invariant steps <= 4 * i + 3
    decreases n - 1 - i
  {
    b := b + [AbsInt(a_list[i] - a_list[i+1])];
    i := i + 1;
    steps := steps + 4;
  }
  var c: seq<int> := [];
  var s := 1;
  var summ := 0;
  i := 0;
  steps := steps + 3;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant |b| == n - 1
    invariant |c| == i
    invariant steps <= 4 * n + 4 * i + 6
    decreases n - 1 - i
  {
    summ := summ + s * b[i];
    s := -s;
    c := c + [summ];
    i := i + 1;
    steps := steps + 4;
  }
  assert steps <= 8 * n + 2;
  SortCostBound(n - 1);
  var sortedC := SortInts(c);
  steps := steps + SortCost(n - 1);
  assert steps <= SortCost(n - 1) + 8 * n + 2;
  var result := if sortedC[0] < 0 then sortedC[n-2] - sortedC[0] else sortedC[n-2];
  output := IntToString(result);
  steps := steps + 4;
  assert steps <= SortCost(n - 1) + 8 * n + 6;
}
