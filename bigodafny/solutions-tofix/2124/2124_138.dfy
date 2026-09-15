// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-16
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop over |queries| reads only queries[i][0], queries[i][1],
//     queries[i][2], a fixed-width row per the problem statement, so no
//     dimension scales with row width; Join and IntToString are linear in
//     output length, giving O(n) overall, same as the Python's two single
//     passes over t queries.
//
//   how this label could be wrong, and what to check:
//     The label assumes query rows have a variable width m, but the
//     problem statement fixes each query line to exactly three integers a,
//     b, k. Open the description's 'three space-separated integers a, b,
//     k' and confirm queries[i] is only ever indexed at 0, 1, 2; if so m
//     is a constant and O(n*m) collapses to O(n).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 20, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1077_A. Frog Jumping  (problem 2124, solution 2124_138)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// all_data = []
// 
// for i in range(t):
//     data = [int(i) for i in input().split(" ")]
//     all_data.append(data)
// 
// for i in all_data:
//     right = i[0]
//     left = i[1]
//     k = i[2]
//     jump = right-left
//     if k % 2 == 0:
//         print(jump*(k//2))
//     else:
//         print(jump*(k//2)+right)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, queries: seq<seq<int>>) returns (output: string)
  requires forall k :: 0 <= k < |queries| ==> |queries[k]| >= 3
{
  var parts: seq<string> := [];
  var i := 0;
  while i < |queries|
  {
    var right := queries[i][0];
    var left := queries[i][1];
    var k := queries[i][2];
    var jump := right - left;
    var kk := FloorDiv(k, 2);
    var val := if k % 2 == 0 then jump * kk else jump * kk + right;
    parts := parts + [IntToString(val)];
    i := i + 1;
  }
  output := if |parts| == 0 then "" else Join(parts, "\n") + "\n";
}
