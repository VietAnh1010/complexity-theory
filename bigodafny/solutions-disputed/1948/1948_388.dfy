// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(logn)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny's only non-constant step is `ISqrt(8 * k + 1)`, charged
//     O(log k) in the input value, followed by one comparison; the Python
//     takes the same root with `math.sqrt`.
//
//   how this label could be wrong, and what to check:
//     The label charges the square root 1, but the model charges `ISqrt(8k
//     + 1)` its O(log k) depth, and the Python takes `sqrt(8*k+1)` at the
//     same point. Check that nothing else loops; then the class is O(log
//     n) in the input value.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 14, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 0, "loops": 0,
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
  requires n >= 0
{
  var k := n;
  var target := 8 * k + 1;
  var s := ISqrt(target);
  if s * s == target {
    output := "YES";
  } else {
    output := "NO";
  }
}
