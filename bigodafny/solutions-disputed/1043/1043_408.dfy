// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over a_list once and per test builds "23" + Repeat("3",
//     m-2), so each test costs O(m) and the total is tests times per-test
//     length, O(n*m), not O(n**2). The Python prints '3' in a `while n>2`
//     loop of the same length per test, so the label is wrong about the
//     Python too.
//
//   how this label could be wrong, and what to check:
//     The label looks for quadratic work, but the loop runs once per test
//     and builds a string of length m. Check Repeat("3", (m - 2) as nat):
//     its cost is the per-test length m, and nothing is nested inside
//     another loop over the same size.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 20, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join", "Repeat"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1326_A. Bad Ugly Numbers  (problem 1043, solution 1043_408)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// t = int(input())
// while t:
//     n = int(input())
//     if n >= 2:    
//         print('23',end="")
//     else: 
//         print("-1")
//     while n>2:
//         print('3',end="")
//         n -= 1
//     print(" ")
//     t -= 1
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    decreases |a_list| - i
  {
    var m := a_list[i];
    if m >= 2 {
      parts := parts + ["23" + Repeat("3", (m - 2) as nat) + " \n"];
    } else {
      parts := parts + ["-1\n \n"];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}
