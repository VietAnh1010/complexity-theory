// 172_A. Phone Code  (problem 1484, solution 1484_82)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// cases = int(input())
//
// numbers = []
// while cases:
//     cases -= 1
//     s = input()
//     numbers.append(s)
//
// numbers.sort()
//
// ct = 0
//
// for i, j in zip(numbers[0], numbers[-1]):
//     if i == j:
//         ct += 1
//     else:
//         print(ct)
//         break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
//
// Prelude.Sort is a plain recursive function (merge sort) with no ghost step
// counter of its own, so its cost is charged as the prelude's SortCost, whose
// recursion mirrors Sort's own split, and bounded by SortCostNLogN -- the
// tight O(k log k) recursion-tree argument.
//
// The final comparison loop walks two strings from `numbers` character by
// character. Its cost is bounded by string length, not by n = |numbers|, so
// the bound below is stated in both n and the total input character count
// (SumLen), via a length-preservation lemma and an elements-of-Sort lemma.

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

lemma MergeElems<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
  ensures forall x :: x in Merge(a, b, less) ==> x in a || x in b
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
  } else if less(b[0], a[0]) {
    MergeElems(a, b[1..], less);
  } else {
    MergeElems(a[1..], b, less);
  }
}

lemma SortElems<T>(s: seq<T>, less: (T, T) -> bool)
  ensures forall x :: x in Sort(s, less) ==> x in s
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortElems(s[..|s| / 2], less);
    SortElems(s[|s| / 2..], less);
    MergeElems(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
  }
}

// Sum of string lengths -- a second, honest measure of input size, since the
// comparison loop's cost is bounded by string length, not by the string count.
ghost function SumLen(xs: seq<string>): nat
{
  if |xs| == 0 then 0 else |xs[0]| + SumLen(xs[1..])
}

lemma SumLenBound(xs: seq<string>, x: string)
  requires x in xs
  ensures |x| <= SumLen(xs)
  decreases |xs|
{
  if xs[0] == x {
  } else {
    SumLenBound(xs[1..], x);
  }
}

method Solve(n: int, numbers: seq<string>) returns (output: string, ghost steps: nat)
  requires |numbers| == n
  requires n >= 1
  ensures steps <= 2 * NLogN(n) + 2 * n + 2 * SumLen(numbers) + 6
{
  SortCostNLogN(n);
  steps := 1 + SortCost(n);

  var sorted := SortStrings(numbers);
  SortLength(numbers, (a, b) => StringLess(a, b));
  assert |sorted| == n;

  var first := sorted[0];
  var last := sorted[|sorted| - 1];

  SortElems(numbers, (a, b) => StringLess(a, b));
  assert first in numbers;
  assert last in numbers;
  SumLenBound(numbers, first);
  SumLenBound(numbers, last);
  assert |first| <= SumLen(numbers);
  assert |last| <= SumLen(numbers);

  var ct := 0;
  var i := 0;
  while i < |first| && i < |last| && first[i] == last[i]
    invariant 0 <= i <= |first|
    invariant steps <= 1 + SortCost(n) + 2 * i
    decreases |first| - i
  {
    ct := ct + 1;
    i := i + 1;
    steps := steps + 2;
  }
  output := IntToString(ct);
  assert i <= |first| <= SumLen(numbers);
  assert steps <= 1 + SortCost(n) + 2 * SumLen(numbers);
  assert SortCost(n) <= 2 * NLogN(n) + 1;
  steps := steps + 1;
}
