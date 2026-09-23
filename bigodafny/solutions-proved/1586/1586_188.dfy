// 433_A. Kitahara Haruki's Gift  (problem 1586, solution 1586_188)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// macas = list(map(int, input().split(" ")))
// macas.sort(reverse=True)
//
// amigo_1 = 0
// amigo_2 = 0
//
// for maca in macas:
//     if amigo_1 <= amigo_2:
//         amigo_1 += maca
//     else:
//         amigo_2 += maca
//
// if amigo_1 == amigo_2:
//     print("YES")
// else:
//     print("NO")
//
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(nlogn), confirmed. The sort is charged SortCost and bounded by the
// prelude's SortCostNLogN, the tight recursion-tree argument. The remaining
// loop is O(n).
method Solve(n: int, scores: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|scores|) + 3 * |scores| + 3
{
  SortCostNLogN(|scores|);
  steps := 1 + SortCost(|scores|);
  var macas := Sort(scores, (x: int, y: int) => x > y);
  SortLength(scores, (x, y) => x > y);
  assert |macas| == |scores|;
  var amigo1 := 0;
  var amigo2 := 0;
  var i := 0;
  while i < |macas|
    invariant 0 <= i <= |macas|
    invariant steps <= 1 + SortCost(|scores|) + 2 * i
    decreases |macas| - i
  {
    if amigo1 <= amigo2 {
      amigo1 := amigo1 + macas[i];
    } else {
      amigo2 := amigo2 + macas[i];
    }
    i := i + 1;
    steps := steps + 2;
  }
  if amigo1 == amigo2 {
    output := "YES";
  } else {
    output := "NO";
  }
  steps := steps + 1;
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
