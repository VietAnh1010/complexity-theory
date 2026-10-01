// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3-05
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Each iteration builds "2" + Repeat("3", v - 1), costing O(v) in the
//     per-test value v, so the total is O(sum of the per-test v_i), not
//     O(number of tests); the Python "3" * (v - 1) pays the same, so the
//     label is wrong, not the translation.
//
//   how this label could be wrong, and what to check:
//     The label O(n) treats n (the number of test cases) as the size. Find
//     Repeat("3", v - 1) in the loop over a_list and check the statement:
//     each v is a per-test digit count up to 10^5 and Repeat is linear in
//     v. If the output length is the real cost, the label omits it; it
//     would only stand if every v were bounded by a literal.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 21, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join", "Repeat"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1326_A. Bad Ugly Numbers  (problem 1043, solution 1043_358)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// for _ in range(n):
//     v = int(input())
//     if v == 1:
//         print(-1)
//     else:
//         print("2" + "3" * (v - 1))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    var v := a_list[i];
    if v == 1 {
      lines := lines + ["-1"];
    } else if v >= 2 {
      lines := lines + ["2" + Repeat("3", v - 1)];
    } else {
      lines := lines + ["2"];
    }
    i := i + 1;
  }
  output := Join(lines, "\n");
}
