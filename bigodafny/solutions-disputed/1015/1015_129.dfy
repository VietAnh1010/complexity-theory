// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny builds `vals := seq(2 * m, ...)` and passes it to
//     JoinInts, which is linear in the output length 2n, a loop to the
//     single integer n; the Python prints 2n numbers from `range(2*n)`
//     too, so O(1) is wrong and O(n) is right.
//
//   how this label could be wrong, and what to check:
//     The label assumes the arithmetic-only body is constant. Check the
//     problem: the output lists 2n numbers for n up to 10^5, so the
//     Dafny's seq of 2*m values and JoinInts, and the Python's generator
//     over range(2*n), both scale with the value n.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 12, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["JoinInts"], "loop_depth": 0,
//     "loops": 0, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1205_A. Almost Equal  (problem 1015, solution 1015_129)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// n*=n%2
// print('YNEOS'[n<1::2],*(i%n*2+i%2+1for i in range(2*n)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var m := if n % 2 == 1 then n else 0;
  if m < 1 {
    output := "NO\n";
  } else {
    var vals := seq(2 * m, i requires 0 <= i < 2 * m => (i % m) * 2 + i % 2 + 1);
    output := "YES " + JoinInts(vals, " ") + "\n";
  }
}
