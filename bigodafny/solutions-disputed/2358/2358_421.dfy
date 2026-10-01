// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r3-13
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     Solve calls IntSqrt2358b(v) for each non-negative element, looping
//     about sqrt(v) times, so the Dafny costs O(n sqrt(max a_i)) in
//     values, whereas the Python's int(i ** 0.5) is O(1) per element and
//     gives the labelled O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes O(1) per element. Open IntSqrt2358b: its loop
//     `while (r + 1) * (r + 1) <= x` runs about sqrt(v) times per element
//     v, a value term the label does not account for. The Python uses i **
//     0.5 once per element in O(1), so the O(n) label fits the Python and
//     the Dafny's sqrt search is the fault.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 31, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
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
      var r := IntSqrt2358b(v);
      notSquare := r * r != v;
    }
    if (v < 0 || notSquare) && v > maxim {
      maxim := v;
    }
    i := i + 1;
  }
  output := IntToString(maxim);
}

method IntSqrt2358b(x: int) returns (r: int)
{
  r := 0;
  while (r + 1) * (r + 1) <= x
    decreases x - r
  {
    r := r + 1;
  }
}
