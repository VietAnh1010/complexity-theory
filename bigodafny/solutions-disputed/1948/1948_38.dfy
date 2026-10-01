// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The only loop in Solve increments m by 1 while 2*a > m*m+m, so it
//     runs about sqrt(2n) iterations in the input VALUE n, and the Python
//     has the identical loop; the true cost is O(sqrt n), outside the
//     vocabulary and below the O(n) label.
//
//   how this label could be wrong, and what to check:
//     The label O(n) treats the single integer n as the loop bound, but
//     the loop only runs until m*m+m reaches 2n, about sqrt(2n) times.
//     Open the Dafny while loop `while 2 * a > m * m + m` and the Python
//     `while 2*a>n**2+n` and check that m advances by 1 per iteration; if
//     so the cost is O(sqrt n), not O(n). If a reviewer accepts any
//     value-bounded loop as O(n) the label stands.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 18, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 0, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 47_A. Triangular numbers  (problem 1948, solution 1948_38)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = int(input())
// n = 1
// 
// while 2*a>n**2+n:
// 	n +=1
// 
// if (2*a)-(n**2+n)==0:
// 	print("YES")
// else:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
  decreases *
{
  var a := n;
  var m := 1;
  while 2 * a > m * m + m
    decreases *
  {
    m := m + 1;
  }
  if 2 * a - (m * m + m) == 0 {
    output := "YES";
  } else {
    output := "NO";
  }
}
