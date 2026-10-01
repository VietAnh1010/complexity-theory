// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n*m)
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-r3d-03
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     For each of the b letters the Dafny runs `while j < |x|` over all
//     a+1 prefix sums counting x[j] <= v, so it costs O(a*b); the Python's
//     bisect is O(log n) per letter (O(n+m log n) overall, close to the
//     label), so the binary search was replaced by a linear scan.
//
//   how this label could be wrong, and what to check:
//     The label assumes a binary search per letter. The Python uses
//     `bisect(x, v)` which is logarithmic, but check whether the Dafny's
//     inner `while j < |x|` counting scan over the whole prefix array for
//     each letter replaces it.
//
//   structural facts (deterministic, from label_audit.py):
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
