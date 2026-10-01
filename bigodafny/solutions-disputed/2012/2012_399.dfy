// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loops i < n once, reading pairs[i][0] and pairs[i][1] with
//     O(1) arithmetic, so it is O(n); the Python also parses a 2-element
//     list per line and takes max/min of scalars, so there is no m term.
//
//   how this label could be wrong, and what to check:
//     The label O(n*m) assumes row width matters, but each pair has
//     exactly two integers (f_i, t_i) and the loop only reads pairs[i][0]
//     and pairs[i][1]. Check the statement: each of the n lines has two
//     integers, so m is the constant 2.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 22, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 276_A. Lunch Rush  (problem 2012, solution 2012_399)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// X = list(map(int, input().split()))
// MAX = -10**9
// for i in range(X[0]):
//     Y = list(map(int, input().split()))
//     MAX = max(MAX, min(Y[0], Y[0] - (Y[1] - X[1])))
// print(MAX)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, pairs: seq<seq<int>>) returns (output: string)
  requires n <= |pairs|
  requires forall idx :: 0 <= idx < |pairs| ==> |pairs[idx]| == 2
{
  var mx := -1000000000;
  var i := 0;
  while i < n
    invariant 0 <= i
    decreases n - i
  {
    var a := pairs[i][0];
    var b := pairs[i][1];
    var v := if a < a - (b - k) then a else a - (b - k);
    if v > mx {
      mx := v;
    }
    i := i + 1;
  }
  output := IntToString(mx);
}
