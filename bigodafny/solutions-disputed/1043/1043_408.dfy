// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r2-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop over a_list (t=n test cases) calls Repeat("3", m-2) whose
//     argument is the per-test digit count m, capped by the problem's
//     stated bound that the sum of m across all test cases never exceeds
//     1e5, so this per-test cost is bounded independent of n and the total
//     is O(n), not O(n**2); the Python's identical while-loop over the
//     same capped m shows the same growth.
//
//   how this label could be wrong, and what to check:
//     The label assumes total print work scales with n**2, as if the
//     number of test cases and the per-test digit value both grow
//     together. Check the description's line 'sum of n for all test cases
//     does not exceed 1e5': since that caps the Repeat/print cost
//     independent of |a_list|, increasing the number of test cases while
//     holding that sum fixed should not increase total work quadratically.
//     If a reviewer can construct a valid input where both the test-case
//     count and the total digit-sum grow together without violating that
//     cap, the O(n) verdict is wrong instead.
//
//   structural facts (deterministic, from labelaudit.py):
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
