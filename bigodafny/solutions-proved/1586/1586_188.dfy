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

// ---- proof-only scaffolding for the complexity bound ----------------
// Prelude.Sort is a plain recursive function (merge sort); it carries no
// ghost step counter (prelude.dfy is off limits), so its cost is charged as
// an opaque-but-defined SortCost mirroring Sort's own split. The bound proved
// here is an honest O(k^2) -- weaker than merge sort's true O(k log k) -- so
// the row's proved complexity does not match its O(nlogn) label.
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

// Label O(nlogn) -- disagrees with the proof below, which only establishes
// O(n^2) (SortCost's honest bound; the tight recursion-tree argument for
// merge sort's O(n log n) is not attempted here). The remaining loop is O(n).
method Solve(n: int, scores: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |scores| * |scores| + 3 * |scores| + 3
{
  SortCostBound(|scores|);
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
