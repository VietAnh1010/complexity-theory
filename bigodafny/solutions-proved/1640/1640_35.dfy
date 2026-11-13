// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     After `MaxSeq` the Dafny calls `Gcd(g, m - a_list[i])` for each of n
//     elements, each charged O(log) in the values, so the cost is O(n log
//     max a_i); the Python's `gcd(g, m - i)` loop pays the same.
//
//   how this label could be wrong, and what to check:
//     The label charges each gcd 1. Check the loop calling `Gcd(g, m -
//     a_list[i])` per element: each call costs Euclid's depth in the
//     values, a value term. The Python's `math.gcd` runs Euclid too, so
//     the label omits it.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 53, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Gcd", "IntToString", "MaxSeq",
//     "MaxSeqFrom"], "loop_depth": 1, "loops": 2, "recursive_helpers": 2,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1216_D. Swords  (problem 1640, solution 1640_35)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import gcd
// n = int(input())
// A = list(map(int, input().split()))
// m = max(A)
// g = 0
// for i in A:
//     g = gcd(g, m - i)
// ans = 0
// for i in A:
//     ans += (m - i) // g
// print(ans, g)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MaxSeqFromBound(s: seq<int>, i: nat, best: int)
  requires i <= |s|
  ensures MaxSeqFrom(s, i, best) >= best
  ensures forall k :: i <= k < |s| ==> s[k] <= MaxSeqFrom(s, i, best)
  decreases |s| - i
{
  if i < |s| {
    MaxSeqFromBound(s, i + 1, if s[i] > best then s[i] else best);
  }
}

lemma GcdPos(a: int, b: int)
  requires a >= 0 && b >= 0
  requires a > 0 || b > 0
  ensures Gcd(a, b) > 0
  decreases b
{
  if b > 0 {
    GcdPos(b, a % b);
  }
}

ghost function SumLogDiff(s: seq<int>, m: int, n: nat): nat
  requires n <= |s|
  decreases n
{
  if n == 0 then 0 else SumLogDiff(s, m, n - 1) + BitLen(m - s[n - 1])
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires exists j, k :: 0 <= j < |a_list| && 0 <= k < |a_list| && a_list[j] != a_list[k]
  ensures steps <= 2 * SumLogDiff(a_list, MaxSeq(a_list), |a_list|) + 17 * |a_list| + 10 + |output|
{
  var m := MaxSeq(a_list);
  steps := 2 + |a_list|;
  MaxSeqFromBound(a_list, 1, a_list[0]);
  assert forall k :: 0 <= k < |a_list| ==> a_list[k] <= m;
  var g := 0;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant g >= 0
    invariant g == 0 ==> forall k :: 0 <= k < i ==> a_list[k] == m
    invariant steps <= 2 + |a_list| + 8 * i + 2 * SumLogDiff(a_list, m, i)
    decreases |a_list| - i
  {
    if g > 0 || m - a_list[i] > 0 {
      GcdPos(g, m - a_list[i]);
    }
    GcdStepsBound(g, m - a_list[i]);
    steps := steps + 6 + GcdSteps(g, m - a_list[i]);
    g := Gcd(g, m - a_list[i]);
    i := i + 1;
  }
  assert g > 0;
  var ans := 0;
  i := 0;
  ghost var base := steps;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps <= base + 8 * i
    decreases |a_list| - i
  {
    ans := ans + (m - a_list[i]) / g;
    i := i + 1;
    steps := steps + 8;
  }
  output := IntToString(ans) + " " + IntToString(g);
  IntToStringDigits(ans);
  IntToStringDigits(g);
  steps := steps + Digits(ans) + Digits(g) + 1;
}
