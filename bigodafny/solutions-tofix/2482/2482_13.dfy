// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(1)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-19
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The while loop increments n until n*(N-1)+1 >= M, but the
//     description caps A and B at 2..20 and 1..20, so the loop is bounded
//     by a constant, not by any sequence length, making this O(1) rather
//     than O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes n scales with an input size, but seq_args=0 and
//     the only quantities are N and M. Check the description's Constraints
//     section: it caps A (N) and B (M) at 20 each; if so the while loop
//     n*(N-1)+1<M runs at most ~20 times regardless of any collection
//     size, so the label should be O(1).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 13, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// p02922 AtCoder Beginner Contest 139 - Power Socket  (problem 2482, solution 2482_13)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a,b=map(int,input().split())
// n=0
// while n*(a-1)+1<b:n+=1
// print(n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, M: int) returns (output: string)
  decreases *
{
  var n := 0;
  while n * (N - 1) + 1 < M
    decreases *
  {
    n := n + 1;
  }
  output := IntToString(n);
}
