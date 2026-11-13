// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny builds the prefix array `x` in O(n) and then runs a binary
//     search over it for each of the m queries, O(n + m log n); the
//     Python's `bisect(x, v)` per query is the same search.
//
//   how this label could be wrong, and what to check:
//     The label omits the search: for each of the m letters the Python
//     calls `bisect(x, v)` on the n + 1 prefix sums, O(log n) each. Check
//     the Dafny's inner `while lo < hi` binary search per query; the class
//     is O(n + m log n), not in the vocabulary.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 43, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 2, "loops": 3, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": true, "seq_args": 2,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 978_C. Letters  (problem 1180, solution 1180_39)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from bisect import bisect
// n, m = map(int, input().split())
// x = [1]
// for v in map(int, input().split()):
//     x.append(x[-1] + v)
// for v in map(int, input().split()):
//     i = bisect(x, v) - 1
//     print(i+1, v-x[i]+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string, ghost steps: nat)
  requires a == |c_list|
  requires b == |d_list|
  requires a >= 0
  requires b >= 0
  requires forall k :: 0 <= k < b ==> d_list[k] >= 1
  ensures steps <= 6 * a + 3 + b * (8 * SearchPot(a + 1) + 22) + 3 * |output|
{
  steps := 1;
  var x := [1];
  var i := 0;
  while i < a
    invariant 0 <= i <= a
    invariant |x| == i + 1
    invariant x[0] == 1
    invariant steps == 1 + 6 * i
    decreases a - i
  {
    x := x + [x[|x|-1] + c_list[i]];
    i := i + 1;
    steps := steps + 6;
  }
  var lines: seq<string> := [];
  i := 0;
  ghost var P := SearchPot(a + 1);
  ghost var K := 8 * P + 22;
  ghost var base := steps;
  while i < b
    invariant 0 <= i <= b
    invariant |x| == a + 1
    invariant |lines| == i
    invariant steps <= base + i * K + 2 * SumLen(lines)
    decreases b - i
  {
    ghost var st0 := steps;
    var v := d_list[i];
    // bisect(x, v): first index whose value exceeds v
    var lo := 0;
    var hi := |x|;
    ghost var it: nat := 0;
    steps := steps + 3;
    while lo < hi
      invariant 0 <= lo <= hi <= |x|
      invariant lo >= 1 || hi >= 1
      invariant it + SearchPot(hi - lo) <= SearchPot(|x|)
      invariant steps == st0 + 3 + 8 * it
      decreases hi - lo
    {
      ghost var k := hi - lo;
      var mid := (lo + hi) / 2;
      if v < x[mid] { hi := mid; } else { lo := mid + 1; }
      BisectStep(k, hi - lo);
      it := it + 1;
      steps := steps + 8;
    }
    var idx := lo - 1;
    ghost var line := IntToString(idx + 1) + " " + IntToString(v - x[idx] + 1);
    IntToStringDigits(idx + 1);
    IntToStringDigits(v - x[idx] + 1);
    SumLenSnoc(lines, line);
    lines := lines + [IntToString(idx + 1) + " " + IntToString(v - x[idx] + 1)];
    steps := steps + 2 * |line| + 12;
    i := i + 1;
    CostMulDistrib(i - 1, 1, i, K);
  }
  output := Join(lines, "\n");
  steps := steps + SumLen(lines) + |lines|;
  if b >= 1 { JoinLen(lines, "\n"); }
}
