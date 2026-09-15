// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n*m)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-07
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     For each of the b queries the Dafny runs a nested `while j < |x|`
//     that scans the whole prefix-sum array x (length a+1) linearly,
//     replacing Python's `bisect(x, v)` binary search, so the true cost is
//     O(n*m) while the Python stays O(n + m log n), labelled O(n+m).
//
//   how this label could be wrong, and what to check:
//     The label assumes the Dafny keeps Python's bisect binary search.
//     Open the inner `while j < |x|` loop nested inside the loop over
//     b_list and confirm it scans all of x linearly per query rather than
//     calling a binary-search helper; if so every one of the b queries
//     costs O(a), giving O(a*b).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 44, "data_dependent_loops": 0, "decreases_star":
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

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string)
  requires a == |c_list|
  requires b == |d_list|
  requires a >= 0
  requires b >= 0
  requires forall k :: 0 <= k < b ==> d_list[k] >= 1
{
  var x := [1];
  var i := 0;
  while i < a
    invariant 0 <= i <= a
    invariant |x| == i + 1
    invariant x[0] == 1
    decreases a - i
  {
    x := x + [x[|x|-1] + c_list[i]];
    i := i + 1;
  }
  var lines: seq<string> := [];
  i := 0;
  while i < b
    invariant 0 <= i <= b
    decreases b - i
  {
    var v := d_list[i];
    var cnt := 0;
    var j := 0;
    while j < |x|
      invariant 0 <= j <= |x|
      invariant 0 <= cnt <= j
      invariant j >= 1 ==> cnt >= 1
      decreases |x| - j
    {
      if x[j] <= v { cnt := cnt + 1; }
      j := j + 1;
    }
    var idx := cnt - 1;
    lines := lines + [IntToString(idx + 1) + " " + IntToString(v - x[idx] + 1)];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
