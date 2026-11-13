// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(1)
//   cause          : both
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     The Dafny computes `m := min(a, b)` and branches on `m % 2`, O(1);
//     the Python's while loop decrements r and c until their product is
//     zero, min(r, c) rounds, so the translation replaced the loop with
//     its closed form.
//
//   how this label could be wrong, and what to check:
//     The Python loops `while t != 0`, decrementing r and c once per
//     round, so it runs min(r, c) times: a value term, Theta(min(n, m)),
//     which O(n+m) overstates. The Dafny drops the loop and tests the
//     parity of min(a, b) directly. Check that the Dafny has no loop at
//     all.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 11, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 0, "loops": 0,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 0, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 451_A. Game With Sticks  (problem 536, solution 536_1054)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// r, c = map(int, input().split())
// t = r*c
// 
// 
// 
// i = 0
// while t !=0:
//     r = r-1
//     c=c-1
//     t = r*c
//     i += 1
// 
// 
//     
// if i%2 == 0:
//     print("Malvika")
// else:
//     print("Akshat")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var m := if a <= b then a else b;
  if m % 2 == 0 {
    output := "Malvika";
  } else {
    output := "Akshat";
  }
}
