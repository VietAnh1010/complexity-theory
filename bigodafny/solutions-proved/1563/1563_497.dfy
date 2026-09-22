// 915_A. Garden  (problem 1563, solution 1563_497)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// buckets, length = map(int,input().split())
// data = list(map(int,input().split()))
// data.sort(reverse=True)
// for element in data:
//     if length % element == 0:
//         print(length // element)
//         break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

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

// Sort's own cost via the standard T(k) = T(k/2) + T(k-k/2) + k recurrence,
// bounded O(k log k) -- precedent solutions-proved/1871/1871_156.dfy. The
// scan loop is linear and dominated, so the whole method is O(k log k).

ghost function SortCost(k: nat): nat
  decreases k
{
  if k <= 1 then 1
  else SortCost(k / 2) + SortCost(k - k / 2) + k
}

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

method Solve(n: int, m: int, values: seq<int>) returns (output: string, ghost steps: nat)
  // Python evaluates m % v for the same v; a zero raises ZeroDivisionError.
  requires forall k :: 0 <= k < |values| ==> values[k] != 0
  ensures steps <= 2 * |values| * (CeilLog2(|values|) + 1) + 5 * |values| + |output| + 10
{
  var asc := SortInts(values);
  SortElems(values, (x, y) => x < y);
  SortCostNLogN(|values|);
  steps := 1 + SortCost(|values|);
  assert forall x :: x in asc ==> x in values;
  assert |asc| == |values|;
  var result := 0;
  var found := false;
  var i := |asc| - 1;
  ghost var cnt := 0;
  ghost var base1 := steps;
  while i >= 0 && !found
    invariant -1 <= i < |asc|
    invariant cnt == (|asc| - 1) - i
    invariant steps <= base1 + 3 * cnt
    decreases i + 1
  {
    assert asc[i] in asc;
    if FloorMod(m, asc[i]) == 0 {
      result := FloorDiv(m, asc[i]);
      found := true;
    }
    i := i - 1;
    cnt := cnt + 1;
    steps := steps + 3;
  }
  assert cnt <= |asc|;
  assert steps <= base1 + 3 * |asc|;
  output := IntToString(result);
  steps := steps + |output| + 2;
}
