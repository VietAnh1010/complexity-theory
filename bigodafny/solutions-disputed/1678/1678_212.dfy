// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-05
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The single while loop in Solve runs c/a + 1 times, so the cost is
//     O(c/a), a cost in input values that no label variable accounts for,
//     even though the statement caps c at 10000. The Python's for i in
//     range(c//a+1) pays the same value term, so the label is wrong, not
//     the translation.
//
//   how this label could be wrong, and what to check:
//     The label O(n) names a size that the input does not have: the input
//     is three integers a, b, c with no count line. Check the loop bound
//     limit := c / a + 1 in Solve and the Python's range(c//a+1); if you
//     read c as the problem size n the label could be accepted as a
//     value-as-size case.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 23, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 0, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 633_A. Ebony and Ivory  (problem 1678, solution 1678_212)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a, b, c = map(int, input().split())
// ok = False
// for i in range(c//a+1):
//     #print(c-a*i)
//     #print((c-a*i)%b==0)
//     if c-a*i >= 0 and (c-a*i)%b==0:
//         ok = True
// if ok:
//     print("Yes")
// else:
//     print("No")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(rows: int, columns: int, value: int) returns (output: string)
  requires rows >= 1
  requires columns >= 1
{
  var a := rows;
  var b := columns;
  var c := value;
  var ok := false;
  var limit := c / a + 1;
  var i := 0;
  while i < limit
    invariant 0 <= i
    decreases limit - i
  {
    if c - a * i >= 0 && (c - a * i) % b == 0 {
      ok := true;
    }
    i := i + 1;
  }
  output := if ok then "Yes" else "No";
}
