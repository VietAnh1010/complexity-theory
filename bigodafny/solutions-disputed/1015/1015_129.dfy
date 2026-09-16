// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     When m>=1 (n odd) the seq(2*m, ...) comprehension builds a sequence
//     of length 2m, O(n) work that the loop-counting facts miss because it
//     is a comprehension, not a while loop; Python's generator unpacked
//     into print over range(2*n) does the same O(n) work, so the labelled
//     O(1) is wrong for both.
//
//   structural facts (deterministic, from labelaudit.py):
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
