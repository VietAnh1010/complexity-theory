// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-08
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Repeat("1", c) is linear in the length of the string it builds, c =
//     n/2, so Solve is O(n) in the single integer n that is the problem's
//     size. The Python's '1'*(n//2) and print of that string pay the same
//     O(n), so the O(1) label is wrong, not the translation.
//
//   how this label could be wrong, and what to check:
//     The label assumes the output is built in constant time. Check
//     Repeat("1", c) with c about n/2 and the Python's '1'*(n//2): both
//     produce a string whose length grows with the value n, which is the
//     problem's size.
//
//   structural facts (deterministic, from label_audit.py):
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
