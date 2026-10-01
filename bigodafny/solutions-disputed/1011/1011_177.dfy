// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : other
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r3d-03
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny finds floor(sqrt(n)) with the loop `while (f + 1) * (f +
//     1) <= n`, which runs about sqrt(n) iterations, a value term O(sqrt
//     n); the Python computes `n**0.5` once and has no loop, so O(1) is
//     right for it and the search loop is a reimplemented library call.
//
//   how this label could be wrong, and what to check:
//     The label assumes the square root is a single library call. Compare
//     the Dafny's `while (f + 1) * (f + 1) <= n` search loop against the
//     Python's `rt = n**0.5`; if the Python has no loop on n, the label is
//     right about the Python and the Dafny is slower.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 22, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1099_B. Squares and Segments  (problem 1011, solution 1011_177)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// rt = n**0.5
// 
// if rt % 1> 0.5:
// 	b = int(rt) + 1
// else:
// 	b = int(rt)
// 
// # if rt * rt == n:
// # 	print(int(rt) * 2)
// # else:
// # 	if n > a * b:
// # 		print(max(a,b) * 2)
// # 	else:
// # 		print(a + b)
// 
// q = n // b
// if n % b != 0:
// 	q += 1
// 
// print(q + b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
  requires n >= 1
{
  var f := 0;
  while (f + 1) * (f + 1) <= n
    invariant 0 <= f
    invariant f * f <= n
    invariant f <= n
    decreases n - f
  {
    f := f + 1;
  }
  var b := f;
  if 4 * n > (2 * f + 1) * (2 * f + 1) {
    b := f + 1;
  }
  var q := n / b;
  if n % b != 0 { q := q + 1; }
  output := IntToString(q + b);
}
