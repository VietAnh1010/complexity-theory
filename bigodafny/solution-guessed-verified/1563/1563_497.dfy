// 1563_497 (problem 1563) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(nlogn)
//   proved bound    : |values| * (CeilLog2(|values|) + 1) + 4 * |values| + 10
//   proved class    : unclassified
//   agent verdict   : proves
//   reference label : O(nlogn)
//   prediction correct against the label: True
//   all gates passed: True
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     SortInts/Sort is mergesort over values (n=|values|); the scan loop is
//     O(n), sort dominates
//
//   agent notes:
//     Charged mergesort via shadow SortCost ghost fn, proved SortCost(s) <=
//     |s|*(CeilLog2(|s|)+1) using MulMonoRight/MulDistrib from GUIDE.
//     Charged IntToString via shadow IntToStringCost, bounded by 3 using
//     added requires capping m,values at 100 (matches description
//     1<=ai,k<=100).
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 1563_497
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
// buckets, length = map(int,input().split())
// data = list(map(int,input().split()))
// data.sort(reverse=True)
// for element in data:
//     if length % element == 0:
//         print(length // element)
//         break
// ----------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- ghost cost model for Sort/Merge (mergesort), used only to bound steps ----

ghost function CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }

lemma CeilLog2Monotone(a: nat, b: nat)
  requires a <= b
  ensures CeilLog2(a) <= CeilLog2(b)
  decreases b
{
  if b <= 1 {
  } else if a <= 1 {
  } else {
    CeilLog2Monotone((a + 1) / 2, (b + 1) / 2);
  }
}

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{}

lemma MulDistrib(a: nat, b: nat, k: nat, L: nat)
  requires a + b == k
  ensures a * L + b * L == k * L
{}

ghost function SortCost(s: seq<int>): nat
  decreases |s|
{
  if |s| <= 1 then 1
  else SortCost(s[..|s| / 2]) + SortCost(s[|s| / 2..]) + |s|
}

lemma SortCostBound(s: seq<int>)
  requires |s| >= 1
  ensures SortCost(s) <= |s| * (CeilLog2(|s|) + 1)
  decreases |s|
{
  if |s| == 1 {
  } else {
    var k := |s|;
    var a := s[..k / 2];
    var b := s[k / 2..];
    assert |a| == k / 2;
    assert |b| == k - k / 2;
    assert k - k / 2 == (k + 1) / 2;
    SortCostBound(a);
    SortCostBound(b);
    CeilLog2Monotone(|a|, |b|);
    assert CeilLog2(k) == 1 + CeilLog2((k + 1) / 2);
    assert CeilLog2(|b|) + 1 == CeilLog2(k);
    MulMonoRight(|a|, CeilLog2(|a|) + 1, CeilLog2(k));
    MulDistrib(|a|, |b|, k, CeilLog2(k));
  }
}

// ---- ghost cost model for IntToString ----

ghost function IntToStringCost(x: int): nat
  decreases if x < 0 then 1 - x else x
{
  if x < 0 then 1 + IntToStringCost(-x)
  else if x < 10 then 1
  else 1 + IntToStringCost(x / 10)
}

lemma IntToStringCostBound2(x: int)
  requires 0 <= x <= 99
  ensures IntToStringCost(x) <= 2
{}

lemma IntToStringCostBound(x: int)
  requires 0 <= x <= 999
  ensures IntToStringCost(x) <= 3
{
  if x < 10 {
  } else {
    IntToStringCostBound2(x / 10);
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

method Solve(n: int, m: int, values: seq<int>) returns (output: string, ghost steps: nat)
  // Python evaluates m % v for the same v; a zero raises ZeroDivisionError.
  requires forall k :: 0 <= k < |values| ==> values[k] != 0
  // description.md: "1 <= n, k <= 100" and "1 <= ai <= 100"
  requires |values| >= 1
  requires 1 <= m <= 100
  requires forall k :: 0 <= k < |values| ==> 1 <= values[k] <= 100
  ensures steps <= |values| * (CeilLog2(|values|) + 1) + 4 * |values| + 10
{
  steps := 1;
  var asc := SortInts(values);
  SortCostBound(values);
  steps := steps + SortCost(values);
  SortElems(values, (x, y) => x < y);
  assert forall x :: x in asc ==> x in values;
  var result := 0;
  var found := false;
  var i := |asc| - 1;
  while i >= 0 && !found
    invariant -1 <= i < |asc|
    invariant steps <= 1 + SortCost(values) + 4 * (|asc| - 1 - i)
    invariant 0 <= result <= 100
    decreases i + 1
  {
    assert asc[i] in asc;
    assert asc[i] in values;
    ghost var kk :| 0 <= kk < |values| && values[kk] == asc[i];
    assert 1 <= asc[i] <= 100;
    if FloorMod(m, asc[i]) == 0 {
      result := FloorDiv(m, asc[i]);
      found := true;
      assert 0 <= result <= 100;
    }
    i := i - 1;
    steps := steps + 4;
  }
  output := IntToString(result);
  IntToStringCostBound(result);
  steps := steps + IntToStringCost(result);
}
