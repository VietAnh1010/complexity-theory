// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop `while a * b < n` alternately increments a and b, so it
//     stops after roughly 2*sqrt(n) iterations in the input value n; the
//     Python has the identical loop, so the true class is O(sqrt n), which
//     is below the labelled O(n).
//
//   how this label could be wrong, and what to check:
//     The label treats the loop as running n times. Trace `while a * b <
//     n` in the Python: a and b grow alternately by 1, so a*b reaches n
//     after about 2*sqrt(n) steps, not n. If you read n as the value the
//     loop runs to, check whether sqrt(n) iterations still counts as O(n)
//     for this dataset.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 13, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1099_B. Squares and Segments  (problem 1011, solution 1011_368)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # http://codeforces.com/contest/1099/problem/B
// n = int(input())
// a = b = 1
// while a * b < n:
//     if a < b:
//         a += 1
//     else:
//         b += 1
// 
// print(a+b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var a := 1;
  var b := 1;
  while a * b < n
    decreases n - a * b
  {
    if a < b { a := a + 1; } else { b := b + 1; }
  }
  output := IntToString(a + b);
}
