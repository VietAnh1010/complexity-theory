// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop `while m > k` subtracts k and increments k each pass, so it
//     stops after about sqrt(2n) iterations, a value term of O(sqrt n),
//     not O(n); the Python has the identical loop.
//
//   how this label could be wrong, and what to check:
//     The label treats the value n as the loop size, but the loop may run
//     only about sqrt(2n) times. Read the while loop in Solve: m drops by
//     k while k grows by 1, so the iteration count k satisfies k(k-1)/2 <
//     n. If a reviewer accepts a value-bounded O(n) as an upper bound, the
//     label stands; if tight classes are required it is O(sqrt n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 13, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 622_A. Infinite Sequence  (problem 5, solution 5_100)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// k=1
// while(n>k):
//    n-=k
//    k+=1
// print(n)
//    
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var m, k := n, 1;
  while m > k
    decreases m - k
  {
    m := m - k;
    k := k + 1;
  }
  output := IntToString(m) + "\n";
}
