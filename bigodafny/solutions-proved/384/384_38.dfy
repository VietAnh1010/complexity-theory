// 59_B. Fortune Telling  (problem 384, solution 384_38)
// time complexity: O(nlogn)
// python exact-diff baseline: exact

include "../../prelude.dfy"
import opened Prelude

function SumSeq(xs: seq<int>): int
  decreases |xs|
{
  if |xs| == 0 then 0 else xs[0] + SumSeq(xs[1..])
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

method Solve(v_0: int, v_1: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |v_1| * (CeilLog2(|v_1|) + 1) + 6 * |v_1| + 10
{
  steps := 1;
  SortCostTreeBound(|v_1|);
  var arr := SortInts(v_1);
  SortLength(v_1, (a: int, b: int) => a < b);
  steps := steps + SortCost(|v_1|);
  var total := SumSeq(arr);
  steps := steps + |arr| + 1;
  if total % 2 == 1 {
    output := IntToString(total);
    steps := steps + 1;
  } else {
    var found := false;
    var ans := 0;
    var i := 0;
    ghost var stepsBefore := steps;
    while i < |arr| && !found
      invariant 0 <= i <= |arr|
      invariant steps <= stepsBefore + 3 * i
      decreases |arr| - i
    {
      if arr[i] % 2 == 1 {
        ans := total - arr[i];
        found := true;
      }
      i := i + 1;
      steps := steps + 3;
    }
    output := if found then IntToString(ans) else "0";
    steps := steps + 1;
  }
}
