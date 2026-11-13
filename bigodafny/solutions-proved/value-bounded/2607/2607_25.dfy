// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over the n-1 intervals and for each the inner `while j <
//     hi` marks coordinates a..min(b, y1) with O(1) seq updates; there are
//     also seq(sz) and a final scan to y1. The cost is O(n * y1 + y1), a
//     value term in the coordinate range, not n squared. The Python's
//     range(a, min(b, y[1])) loop and list(range(y[1])) pay the same.
//
//   how this label could be wrong, and what to check:
//     The label reads the nested loops as n by n, but the inner loop
//     `while j < hi` runs over the coordinate range a to min(b, y1), an
//     input VALUE span, not over n. Check the statement for the coordinate
//     cap and compare with the interval count.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 45, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 3, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 397_A. On Segment's Own Points  (problem 2607, solution 2607_25)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import Counter
// from re import findall
// 
// n = int(input())
// y = [int(i) for i in input().split()]
// alex = list(range(y[1]))
// for i in range(n-1):
//     a, b  = [int(x) for x in input().split()]
//     for j in range(a, min(b, y[1])):
//         alex[j] = 'X'
// 
// o = [str(x) for x in (alex[y[0]:y[1]])]
// o = filter(lambda el: el is not 'X', o)
// 
// print(len(list(o)))
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

ghost function Span2607(a: int, b: int, y1: int): nat
{
  var hi := if b < y1 then b else y1;
  if hi > a then hi - a else 0
}

ghost function TotalSpan2607(iv: seq<seq<int>>, y1: int, k: nat): nat
  requires k <= |iv|
  requires forall q :: 0 <= q < |iv| ==> |iv[q]| >= 2
  decreases k
{
  if k <= 1 then 0 else TotalSpan2607(iv, y1, k - 1) + Span2607(iv[k-1][0], iv[k-1][1], y1)
}

method Solve(n: int, intervals: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n == |intervals|
  requires forall k :: 0 <= k < |intervals| ==> |intervals[k]| >= 2
  requires n >= 1
  ensures steps <= 14 * n + 8 * TotalSpan2607(intervals, intervals[0][1], n)
    + 2 * (if intervals[0][1] > 0 then intervals[0][1] else 0)
    + 10 * (if intervals[0][1] > intervals[0][0] then intervals[0][1] - intervals[0][0] else 0)
    + |output| + 20
{
  steps := 6;
  var y0 := intervals[0][0];
  var y1 := intervals[0][1];
  var sz := if y1 > 0 then y1 else 0;
  steps := steps + 1 + sz;
  var marked := seq(sz, _ => false);
  var k := 1;
  while k < n
    invariant 1 <= k <= n
    invariant |marked| == sz
    invariant steps <= 7 + sz + 12 * (k - 1) + 8 * TotalSpan2607(intervals, y1, k)
    decreases n - k
  {
    var a := intervals[k][0];
    var b := intervals[k][1];
    var hi := if b < y1 then b else y1;
    var j := a;
    ghost var s0 := steps;
    steps := steps + 12;
    while j < hi
      invariant |marked| == sz
      invariant a <= j
      invariant j <= hi || j == a
      invariant steps <= s0 + 12 + 8 * (j - a)
      decreases hi - j
    {
      if 0 <= j < sz {
        marked := marked[j := true];
      }
      j := j + 1;
      steps := steps + 8;
    }
    assert j - a <= Span2607(a, b, y1);
    k := k + 1;
  }
  var cnt := 0;
  var t := y0;
  ghost var s1 := steps;
  while t < y1
    invariant |marked| == sz
    invariant y0 <= t
    invariant t <= y1 || t == y0
    invariant steps <= s1 + 10 * (t - y0)
    decreases y1 - t
  {
    if 0 <= t < sz && !marked[t] {
      cnt := cnt + 1;
    }
    t := t + 1;
    steps := steps + 10;
  }
  output := IntToString(cnt);
  IntToStringDigits(cnt);
  steps := steps + Digits(cnt);
}
