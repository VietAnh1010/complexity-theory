// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The single loop over `a_list` calls `ISqrt(v)` for every nonnegative
//     element, charged its O(log v) depth, so the cost is O(n log max
//     a_i); the Python's `int(i ** 0.5)` takes the same square root.
//
//   how this label could be wrong, and what to check:
//     The label charges each element 1, but each nonnegative element calls
//     `ISqrt(v)`, charged O(log v), a value term; the Python's `i ** 0.5`
//     takes the same root. Check that the loop body is otherwise constant;
//     then the class is O(n log max a_i).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 22, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 914_A. Perfect Squares  (problem 2358, solution 2358_421)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// input()
// ar = list(map(int, input().split()))
// 
// maxim = -10 ** 6
// 
// for i in ar:
//     if (i < 0 or (int(i ** 0.5)) ** 2 != i) and i > maxim:
//         maxim = i
// 
// print(maxim)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var maxim := -1000000;
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    var v := a_list[i];
    var notSquare := true;
    if v >= 0 {
      var r := ISqrt(v);
      notSquare := r * r != v;
    }
    if (v < 0 || notSquare) && v > maxim {
      maxim := v;
    }
    i := i + 1;
  }
  output := IntToString(maxim);
}
