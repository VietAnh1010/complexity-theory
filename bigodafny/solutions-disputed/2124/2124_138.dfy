// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loops once over |queries| doing O(1) arithmetic and
//     FloorDiv per query, then Join, so it is O(n); k enters only through
//     closed-form arithmetic, and the Python loop over t queries is
//     likewise linear.
//
//   how this label could be wrong, and what to check:
//     The label O(n*m) assumes row width varies, but each query is exactly
//     three numbers (a, b, k) and the loop reads queries[i][0..2]. Check
//     the statement: each of the t lines has three space-separated
//     integers.
//
//   structural facts (deterministic, from label_audit.py):
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
