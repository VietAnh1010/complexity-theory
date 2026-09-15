// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r2-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loop `while i < rawN { fact := fact * i; ... }` repeatedly
//     multiplies a growing bignum accumulator by i, and per the cost table
//     int operations whose value grows with n (factorials) are not O(1);
//     the identical `fact *= i` pattern appears in sibling
//     1073_645/1077_84's Factorial function, both labeled O(n**2), so this
//     row's O(n) label undercounts the same bignum-growth pattern.
//
//   how this label could be wrong, and what to check:
//     The label treats each `fact := fact * i` as an O(1) machine-word
//     multiply, but per the cost table's 'factorials... not O(1); bignum'
//     rule the multiplicand grows with i, so total cost should track the
//     other two factorial-computing rows in this same problem (1073_645,
//     1077_84), both labeled O(n**2). Compare this row's single
//     accumulation loop against those two Factorial-recursion rows; if a
//     reviewer judges the growing-digit cost genuinely doesn't apply here
//     (e.g. because n<=20 keeps the accumulator inside machine-word range
//     throughout), the O(n) label should stand instead.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 16, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1433_E. Two Round Dances  (problem 1073, solution 1073_822)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// fact = 1
// n = int(input())
// for i in range(2, n):
//     fact *= i
// print(fact * 2 // n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
  requires n >= 0
{
  var rawN := n + 1;
  var fact := 1;
  var i := 2;
  while i < rawN
    decreases rawN - i
  {
    fact := fact * i;
    i := i + 1;
  }
  output := IntToString(FloorDiv(fact * 2, rawN));
}

