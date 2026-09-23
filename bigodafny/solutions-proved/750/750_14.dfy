// 621_B. Wet Shark and Bishops  (problem 750, solution 750_14)
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

method Solve(n: int, data_points: seq<(int, int)>) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * |data_points| * (CeilLog2(|data_points|) + 1) + 24 * |data_points| + 12
{
  steps := 1;
  var aArr := seq(|data_points|, i requires 0 <= i < |data_points| => data_points[i].0 + data_points[i].1);
  var bArr := seq(|data_points|, i requires 0 <= i < |data_points| => data_points[i].0 - data_points[i].1);
  steps := steps + 2 * |data_points|;
  SortCostTreeBound(|data_points|);
  var aSorted := SortInts(aArr);
  SortLength(aArr, (a: int, b: int) => a < b);
  steps := steps + SortCost(|data_points|);
  SortCostTreeBound(|data_points|);
  var bSorted := SortInts(bArr);
  SortLength(bArr, (a: int, b: int) => a < b);
  steps := steps + SortCost(|data_points|);
  var res := 0;
  var i := 0;
  ghost var stepsBeforeA := steps;
  while i < |aSorted|
    invariant 0 <= i <= |aSorted|
    invariant steps <= stepsBeforeA + 10 * i + 1
    decreases |aSorted| - i
  {
    var cnt := 1;
    while i+1 < |aSorted| && aSorted[i] == aSorted[i+1]
      invariant i < |aSorted|
      invariant steps <= stepsBeforeA + 10 * i + 1
      decreases |aSorted| - i
    {
      cnt := cnt + 1;
      i := i + 1;
      assert i < |aSorted|;
      steps := steps + 4;
    }
    res := res + cnt*(cnt-1)/2;
    i := i + 1;
    steps := steps + 6;
  }
  assert steps <= stepsBeforeA + 10 * |aSorted| + 1;
  i := 0;
  ghost var stepsBeforeB := steps;
  while i < |bSorted|
    invariant 0 <= i <= |bSorted|
    invariant steps <= stepsBeforeB + 10 * i + 1
    decreases |bSorted| - i
  {
    var cnt := 1;
    while i+1 < |bSorted| && bSorted[i] == bSorted[i+1]
      invariant i < |bSorted|
      invariant steps <= stepsBeforeB + 10 * i + 1
      decreases |bSorted| - i
    {
      cnt := cnt + 1;
      i := i + 1;
      assert i < |bSorted|;
      steps := steps + 4;
    }
    res := res + cnt*(cnt-1)/2;
    i := i + 1;
    steps := steps + 6;
  }
  assert steps <= stepsBeforeB + 10 * |bSorted| + 1;
  assert SortCost(|data_points|) <= 2 * |data_points| * (CeilLog2(|data_points|) + 1) + 1;
  assert steps <= 1 + 2 * |data_points| + 2 * SortCost(|data_points|) + 20 * |data_points| + 2;
  assert 2 * SortCost(|data_points|) <= 4 * |data_points| * (CeilLog2(|data_points|) + 1) + 2;
  assert steps <= 4 * |data_points| * (CeilLog2(|data_points|) + 1) + 22 * |data_points| + 5;
  output := IntToString(res);
  steps := steps + 1;
}
