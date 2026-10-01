// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : other
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r3-10
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny loop increments s while s * s < target with target =
//     8*k+1, costing O(sqrt k) in the input value, whereas the Python
//     calls math.sqrt once; the cap n<=500 is a statement bound, not a
//     source literal.
//
//   how this label could be wrong, and what to check:
//     The label treats the check as constant, but the Dafny scans s upward
//     until s*s >= 8k+1, which costs O(sqrt(k)) in the input value. Check
//     the while s * s < target loop (which also needs decreases *) against
//     the Python's single sqrt call; the Python is O(1), so the
//     translation replaced a library call with a search.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 19, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 0, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 47_A. Triangular numbers  (problem 1948, solution 1948_388)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import sqrt
// k=int(input())
// n=(sqrt(8*k+1)-1)/2
// if n>int(n):
// 	print("NO")
// else:
// 	print("YES")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
  decreases *
{
  var k := n;
  var target := 8 * k + 1;
  var s := 0;
  while s * s < target
    decreases *
  {
    s := s + 1;
  }
  if s * s == target {
    output := "YES";
  } else {
    output := "NO";
  }
}
