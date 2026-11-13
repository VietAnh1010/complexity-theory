// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Both programs read only `data[i][1]` (the Python `c.split()[1]`) of
//     each of n two-number queries and print twice it, so the cost is
//     O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes the row width varies. Each query is exactly two
//     integers n and x; the Python splits that fixed two-token line twice.
//     Check the input format; two numbers per line make m a constant and
//     the class O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 17, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1194_A. Remove a Progression  (problem 2627, solution 2627_428)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for k in range(t):
//     c=input()
//     n=int(c.split()[0])
//     x=int(c.split()[1])
//     print(2*x)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, data: seq<seq<int>>) returns (output: string)
  requires n == |data|
  requires forall k :: 0 <= k < |data| ==> |data[k]| >= 2
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    lines := lines + [IntToString(2 * data[i][1])];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
