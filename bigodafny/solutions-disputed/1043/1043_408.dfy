// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over a_list and builds each answer with `Repeat("3",
//     m-2)` then Join, so the cost is O(t + sum of the per-test values
//     m_i), linear in output length; the Python's `while n>2` printing
//     loop is linear in the same sum, so O(n**2) matches neither.
//
//   how this label could be wrong, and what to check:
//     The label assumes a quadratic cost. Check the Python: the inner
//     `while n>2` prints one character per iteration, so the cost per test
//     is its own n_i, and the statement says the sum of n over tests is at
//     most 10^5; nothing in either source is quadratic.
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
