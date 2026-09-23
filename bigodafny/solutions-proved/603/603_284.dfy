// 1041_A. Heist  (problem 603, solution 603_284)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l=list(map(int,input().split()))
// l.sort()
// x=0
// for i in range(n-1):
//     x+=l[i+1]-l[i]-1
// print(x)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
//
// Prelude.Sort is a plain recursive function (merge sort) with no ghost step
// counter of its own, so its cost is charged as the prelude's SortCost, whose
// recursion mirrors Sort's own split (Sort(s) recurses on s[..|s|/2] and
// s[|s|/2..], then Merge is linear in the combined length), and bounded by
// SortCostNLogN -- the tight O(k log k) recursion-tree argument.

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

method Solve(n: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires |numbers| == n
  ensures steps <= 2 * NLogN(n) + 2 * n + 4
{
  SortCostNLogN(n);
  steps := 1 + SortCost(n);

  var l := SortInts(numbers);
  SortLength(numbers, (x, y) => x < y);
  assert |l| == n;

  var x := 0;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n
    invariant i < n - 1 ==> i + 1 < n
    invariant steps <= 1 + SortCost(n) + 2 * i
    decreases n - 1 - i
  {
    x := x + l[i+1] - l[i] - 1;
    i := i + 1;
    steps := steps + 2;
  }
  output := IntToString(x);
  assert steps <= 1 + SortCost(n) + 2 * n;
  assert SortCost(n) <= 2 * NLogN(n) + 1;
  steps := steps + 1;
}
