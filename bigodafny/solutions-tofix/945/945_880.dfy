// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(logn)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny while loop halves m each iteration until m==0, taking
//     O(logn) iterations; Python's bin(x) produces a string of length
//     proportional to the bit-length of x and .count('1') scans it, also
//     O(logn), so the labelled O(1) is wrong for both, not just the
//     translation.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 14, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 579_A. Raising Bacteria  (problem 945, solution 945_880)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// is_debug = False
// 
// x = int(input())
// 
// print(f'{bin(x).count("1")}')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var m := n;
  var count := 0;
  while m > 0
    decreases m
  {
    count := count + m % 2;
    m := m / 2;
  }
  output := IntToString(count) + "\n";
}
