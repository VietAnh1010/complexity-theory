// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(1)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-11
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve(rows, columns, value) has no sequence parameter at all
//     (seq_args is 0) and the while loop runs c/a+1 times, which the
//     description caps at at most 10001 by 1<=c<=10000 and 1<=a<=100, so
//     the loop count is a fixed constant, not a growing n.
//
//   how this label could be wrong, and what to check:
//     The label assumes an unbounded n, but Solve takes only three ints
//     with no seq argument. Check the description's bound 1<=c<=10000,
//     1<=a<=100: if that holds, the loop count c//a+1 is capped by a fixed
//     constant in both the Python range(c//a+1) and the Dafny while, and
//     the true cost is O(1).
//
//   structural facts (deterministic, from labelaudit.py):
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
