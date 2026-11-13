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
//     The Dafny's only non-constant step is `ISqrt(n)`, charged O(log n)
//     in the input value, followed by constant arithmetic; the Python
//     computes the same root with `n**0.5`.
//
//   how this label could be wrong, and what to check:
//     The label charges the square root 1, but the model charges
//     `ISqrt(n)` its O(log n) depth, and the Python takes `n**0.5` at the
//     same point. Check that the rest is straight-line arithmetic; then
//     the class is O(log n) in the input value n.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 15, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 0,
//     "loops": 0, "recursive_helpers": 0, "seq_append_read_in_same_loop":
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
  var f := ISqrt(n);
  ISqrtSpec(n);
  var b := f;
  if 4 * n > (2 * f + 1) * (2 * f + 1) {
    b := f + 1;
  }
  var q := n / b;
  if n % b != 0 { q := q + 1; }
  output := IntToString(q + b);
}
