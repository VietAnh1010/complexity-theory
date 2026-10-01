// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(logn)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops `while m > 0` with m := m / 2, so it runs about log2(x)
//     iterations for the input value x, a value term the model charges
//     even though x <= 10^9. The Python's bin(x).count('1') builds and
//     scans a string of log x characters, so it pays the same cost and the
//     O(1) label is wrong.
//
//   how this label could be wrong, and what to check:
//     The label treats the work as constant, but Solve halves m in `while
//     m > 0` once per bit of the input value x. Check that the Python's
//     bin(x).count('1') also touches every bit of x; the 10^9 cap does not
//     make it constant.
//
//   structural facts (deterministic, from label_audit.py):
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
