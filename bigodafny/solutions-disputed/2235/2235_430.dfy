// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over the t test cases and, per case, steps through s
//     with i := i + 2, appending to buf in O(1); Join is linear in output,
//     so the cost is O(t + sum of |s_i|), a per-test value summed over
//     tests rather than n squared. The Python does the same `for i in
//     range(0, len(s), 2)` per test, so the label is wrong for both.
//
//   how this label could be wrong, and what to check:
//     The label claims quadratic growth, but the two loops are tests (t)
//     times characters per test, i.e. total input length. Check that the
//     inner `while i < |s|` loop runs once per element of s_list with step
//     2 and that nothing else walks s; if n in the label is meant as t
//     times per-test n, the label is a name for the same product and the
//     verdict flips to ok.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 34, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 2, "loops":
//     2, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1400_A. String Similarity  (problem 2235, solution 2235_430)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #Written by Shagoto
// 
// t = int(input())
// for x in range(t):
//     n = int(input())
//     s = input()
//     
//     if(n == 1):
//         print(s)
//     
//     else:
//         for i in range(0, len(s), 2):
//             print(s[i], end = "")
//         print()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(t: int, n_list: seq<int>, s_list: seq<string>) returns (output: string)
  requires t <= |n_list|
  requires t <= |s_list|
{
  var parts: seq<string> := [];
  var x := 0;
  while x < t
    invariant 0 <= x
    decreases t - x
  {
    var n := n_list[x];
    var s := s_list[x];
    var line: string;
    if n == 1 {
      line := s;
    } else {
      var buf: string := "";
      var i := 0;
      while i < |s|
        invariant 0 <= i
        decreases |s| - i
      {
        buf := buf + [s[i]];
        i := i + 2;
      }
      line := buf;
    }
    parts := parts + [line];
    x := x + 1;
  }
  output := Join(parts, "\n");
}
