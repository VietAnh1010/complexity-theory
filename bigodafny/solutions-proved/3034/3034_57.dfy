// 1150_C. Prefix Sum Primes  (problem 3034, solution 3034_57)
// time complexity: O(nlogn)
// python exact-diff baseline: exact

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
  ensures steps <= 2 * |a_list| * (CeilLog2(|a_list|) + 1) + 8 * |a_list| + 10
{
  steps := 1;
  var y := a_list;
  if |y| == 0 {
    output := "";
    steps := steps + 1;
    return;
  }
  if n == 1 {
    output := IntToString(y[0]);
    steps := steps + 1;
    return;
  }
  var even := 0;
  var odd := 0;
  var i := 0;
  while i < |y|
    invariant 0 <= i <= |y|
    invariant steps <= 1 + 2 * i
    decreases |y| - i
  {
    if y[i] == 2 {
      even := even + 1;
    } else if y[i] == 1 {
      odd := odd + 1;
    }
    i := i + 1;
    steps := steps + 2;
  }
  if even == 0 || odd == 0 {
    output := JoinInts(y, " ");
    steps := steps + |y| + 1;
    return;
  }
  SortCostTreeBound(|y|);
  ghost var stepsBeforeSort := steps;
  var sorted := Sort(y, (a: int, b: int) => a > b);
  SortLength(y, (a: int, b: int) => a > b);
  steps := steps + SortCost(|y|);
  i := 0;
  ghost var stepsBeforeFind := steps;
  while i < |sorted| && sorted[i] != 1
    invariant 0 <= i <= |sorted|
    invariant steps <= stepsBeforeFind + 2 * i
    decreases |sorted| - i
  {
    i := i + 1;
    steps := steps + 2;
  }
  if i >= |sorted| || |sorted| < 2 {
    output := JoinInts(sorted, " ");
    steps := steps + |sorted| + 1;
    return;
  }
  var t := sorted[i];
  sorted := sorted[i := sorted[1]];
  sorted := sorted[1 := t];
  output := JoinInts(sorted, " ");
  steps := steps + 2 + |sorted| + 1;
}
