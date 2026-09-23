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

// Label O(nlogn), confirmed. The sort is charged SortCost and bounded by the
// prelude's SortCostWithin, the tight recursion-tree argument. The
// pairs/output builders are O(n); JoinInts is charged a flat O(1) per element (IntToString's
// digit-count growth is not the point of this row and is not tracked).
method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|a_list|) + 6 * |a_list| + 5
{
  var pairs := seq(|a_list|, i requires 0 <= i < |a_list| => (a_list[i], i));
  SortCostWithin(|pairs|, |a_list|);
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
