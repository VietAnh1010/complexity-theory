// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-22
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     output := Repeat("1", c) builds a string of length about n/2, which
//     the table charges O(length of argument), and the Python's '1'*(n//2)
//     allocates the same length string, so both are O(n) and the O(1)
//     label undercounts the output-size cost on both sides.
//
//   how this label could be wrong, and what to check:
//     The label assumes building the output string is free. Check that
//     Repeat("1", c) with c around n/2 is O(length of argument) per the
//     cost table, so the Dafny is O(n); then check the Python's '1'*(n//2)
//     string multiplication, which also allocates a string of length ~n/2
//     and is O(n) in CPython, so this is not a translation gap either.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 14, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Repeat"], "loop_depth": 0, "loops":
//     0, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 0, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 774_C. Maximum Number  (problem 2880, solution 2880_23)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// if n % 2 == 0:
//     print('1'*(n//2))
// else:
//     print('7'+'1'*((n-3)//2))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  if n % 2 == 0 {
    var raw := n / 2;
    var c := if raw < 0 then 0 else raw;
    output := Repeat("1", c);
  } else {
    var raw := (n - 3) / 2;
    var c := if raw < 0 then 0 else raw;
    output := "7" + Repeat("1", c);
  }
}
