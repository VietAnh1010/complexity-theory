// 624_B. Making a String  (problem 209, solution 209_103)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(sorted(map(int, input().split()), reverse=True))
// for i in range(n - 1):
//     a[i + 1] = max(0, min(a[i] - 1, a[i + 1]))
// print(sum(a))
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

method Solve(N: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires N == |numbers|
  ensures steps <= SortCost(N) + 7 * N + 10
{
  steps := 1;
  SortCostBound(N);
  var a := Sort(numbers, (x, y) => x > y);
  SortLength(numbers, (x, y) => x > y);
  steps := steps + SortCost(N);
  var i := 0;
  while i < N - 1
    invariant 0 <= i <= N
    invariant |a| == N
    invariant steps <= 5 * i + SortCost(N) + 1
    decreases N - 1 - i
  {
    var cand := a[i] - 1;
    if a[i + 1] < cand { cand := a[i + 1]; }
    if cand < 0 { cand := 0; }
    a := a[i + 1 := cand];
    i := i + 1;
    steps := steps + 5;
  }
  var total := 0;
  var j := 0;
  steps := steps + 1;
  while j < |a|
    invariant 0 <= j <= |a|
    invariant steps <= 5 * N + SortCost(N) + 2 * j + 2
    decreases |a| - j
  {
    total := total + a[j];
    j := j + 1;
    steps := steps + 2;
  }
  output := IntToString(total);
  steps := steps + 1;
}
