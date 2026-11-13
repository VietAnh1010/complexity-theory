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
//     The Dafny's only non-constant step is `ISqrt(1 + 8 * num)`, charged
//     O(log n) in the input value, with straight-line arithmetic around
//     it; the Python takes the same square root with `math.sqrt`.
//
//   how this label could be wrong, and what to check:
//     The label charges the square root 1, but the model charges
//     `ISqrt(m)` its O(log m) recursion depth, and the Python takes
//     `math.sqrt(1 + 8*num)` at the same point. Check that the rest is
//     straight-line arithmetic; then the class is O(log n) in the input
//     value n.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 16, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 0,
//     "loops": 0, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 622_A. Infinite Sequence  (problem 5, solution 5_25)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// number = input()
// current = 0
// num = int(number)
// D = math.sqrt(1 + 8*num)
// n = ( D - 1 )/2
// n = int(n)
// summa = n*(n+1)/2
// if num == summa:
// 	n-=1
// 	summa = n*(n+1)/2
// if num>summa:
// 	num -= summa
// num = int (num)
// print (num)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var num := n;
  var m := 1 + 8 * num;
  var d: int := ISqrt(m);
  var k := (d - 1) / 2;
  var summa := k * (k + 1) / 2;
  if num == summa {
    k := k - 1;
    summa := k * (k + 1) / 2;
  }
  var result := num - summa;
  output := IntToString(result);
}
