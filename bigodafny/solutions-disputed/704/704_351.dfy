// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : other
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r3-04
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny's while loop with `(m+1)*(m+2) <= 2*prob` iterates
//     O(sqrt(k)) times in the input value k (parameter b), a sqrt search;
//     the Python computes math.floor(math.sqrt(...)) once, so it is O(1)
//     as labelled.
//
//   how this label could be wrong, and what to check:
//     The label assumes no loop depends on an input. The Dafny replaced
//     Python's single math.sqrt call with a search loop `while fuel > 0 &&
//     (m+1)*(m+2) <= 2*prob`. Check that prob = FloorDiv(240 - b, 5) comes
//     from the input k, so the loop runs about sqrt(2*prob) times; the cap
//     k <= 240 does not make it constant under the value-term rule.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 17, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 750_A. New Year and Hurry  (problem 704, solution 704_351)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// n, k = map(int, input().split())
// 
// timeToSolve = 240 - k
// problems = math.floor(timeToSolve / 5)
// problems = math.floor((math.sqrt(1 + 8*problems) - 1) / 2)
// 
// print(n if problems > n else problems)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var timeToSolve := 240 - b;
  var prob := FloorDiv(timeToSolve, 5);
  var m := 0;
  var fuel := (if prob > 0 then prob else 0) + 2;
  while fuel > 0 && (m+1)*(m+2) <= 2*prob
    decreases fuel
  {
    m := m + 1;
    fuel := fuel - 1;
  }
  var ans := if m > a then a else m;
  output := IntToString(ans);
}
