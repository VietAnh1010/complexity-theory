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
  ensures steps <= 2 * NLogN(N) + 1 + 7 * N + 10
{
  steps := 1;
  SortCostNLogN(N);
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
