// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The while loop `a*b < n` alternately increments the smaller of a and
//     b, so both a and b converge to about sqrt(n) and the loop runs
//     O(sqrt(n)) times; Python implements the identical loop, so both
//     languages are O(sqrt(n)), not the labelled O(n), which is a label
//     error.
//
//   structural facts (deterministic, from labelaudit.py):
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
