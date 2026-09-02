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
// Prelude.Sort is a plain recursive function (merge sort); it carries no
// ghost step counter of its own (prelude.dfy is off limits), so its cost is
// charged as an opaque-but-defined function SortCost whose recursion mirrors
// Sort's own split. This copy proves the true O(k log k) by a recursion-tree
// argument over a ceiling log; solutions-verified/ keeps the weaker O(k^2)
// bound on it -- weaker than the true O(k log k) of merge sort.
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
  var d := k - 2 * L; // d is 0 or 1
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

// ---- n log n recursion-tree argument -------------------------------------
// Ceiling log. The recursive step is ceil(n/2), not floor(n/2), which is what
// makes the induction close: both halves of a split of size k are at most
// ceil(k/2), and CeilLog2(ceil(k/2)) = CeilLog2(k) - 1 holds by definition.
// With floor-log that step is false at k = 3.
ghost function CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }

lemma CeilLog2Monotone(m: nat, n: nat)
  requires m <= n
  ensures CeilLog2(m) <= CeilLog2(n)
  decreases n
{
  if n <= 1 { }
  else if m <= 1 { }
  else { CeilLog2Monotone((m + 1) / 2, (n + 1) / 2); }
}

// Z3 does not do nonlinear arithmetic well. Every multiplication step the main
// proof needs is isolated here so the solver never has to discover one.
lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

lemma MulDistrib(a: nat, b: nat, k: nat, L: nat)
  requires a + b == k
  ensures a * L + b * L == k * L
{ }

lemma SortCostNLogN(k: nat)
  ensures SortCost(k) <= 2 * k * (CeilLog2(k) + 1) + 1
  decreases k
{
  if k <= 1 { return; }
  var a := k / 2;
  var b := k - k / 2;
  var L := CeilLog2(k);
  assert a + b == k;
  assert b == (k + 1) / 2;
  assert a <= b;
  SortCostNLogN(a);
  SortCostNLogN(b);
  CeilLog2Monotone(a, b);
  assert L == 1 + CeilLog2(b);
  assert CeilLog2(a) + 1 <= L;
  assert CeilLog2(b) + 1 == L;
  MulMonoRight(2 * a, CeilLog2(a) + 1, L);
  MulMonoRight(2 * b, CeilLog2(b) + 1, L);
  assert SortCost(a) <= 2 * a * L + 1;
  assert SortCost(b) <= 2 * b * L + 1;
  MulDistrib(2 * a, 2 * b, 2 * k, L);
  assert 2 * a * L + 2 * b * L == 2 * k * L;
  assert SortCost(k) == SortCost(a) + SortCost(b) + k;
  assert SortCost(k) <= 2 * k * L + k + 2;
  assert 2 * k * (L + 1) == 2 * k * L + 2 * k;
  assert k + 2 <= 2 * k + 1;
}

method Solve(n: int, numbers: seq<string>) returns (output: string, ghost steps: nat)
  requires |numbers| == n
  requires n >= 1
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 2 * n + 2 * SumLen(numbers) + 6
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
  assert SortCost(n) <= 2 * n * (CeilLog2(n) + 1) + 1;
  steps := steps + 1;
}
