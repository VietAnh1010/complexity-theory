// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve makes one pass over the n pairs and reads only l[0] and l[1],
//     with O(1) arithmetic and IntToString, and Join over the n parts is
//     linear in output; no row is ever walked, so it is O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes variable row width m. Check the statement: each
//     test line has exactly two integers a and b; Solve reads only
//     pairs[i][0] and pairs[i][1] and the Python splits a two-token line.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 25, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1328_A. Divisibility Problem  (problem 171, solution 171_82)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// num = int(input())
// 
// for i in range(num):
//     l = input().split()
//     a = int(l[0])
//     b = int(l[1])
// 
//     if a % b == 0:
//         print(0)
//     else:
//         print(int(b - (a % b)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
  requires n >= 0
  requires |pairs| == n
  requires forall idx :: 0 <= idx < |pairs| ==> |pairs[idx]| >= 2 && pairs[idx][1] != 0
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var l := pairs[i];
    var a := l[0];
    var b := l[1];
    if a % b == 0 {
      parts := parts + [IntToString(0)];
    } else {
      parts := parts + [IntToString(b - (a % b))];
    }
    i := i + 1;
  }
  output := Join(parts, "\n");
}
