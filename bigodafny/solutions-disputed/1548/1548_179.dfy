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
//     Both programs read only the three fixed entries of each of n query
//     rows and compute one answer with a division, so the cost is O(n); a
//     row is never walked.
//
//   how this label could be wrong, and what to check:
//     The label assumes row width varies. Each query is exactly three
//     integers l, r, d, read as `a[i][0]`, `a[i][1]`, `a[i][2]`. Check the
//     input format; three numbers per line make m a constant and the class
//     O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 26, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1101_A. Minimum Integer  (problem 1548, solution 1548_179)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def minint(n, a):
//     for i in range(n):
//         l=a[i][0]
//         r=a[i][1]
//         d=a[i][2]
//         if  l<= d<=r:
//             print((r//d+1)*d)
//         else:
//             print(d)
// n=int(input())
// v=[]
// for i in range(n):
//     a = input().strip().split()
//     a = list(map(int, a))
//     v.append(a)
// minint(n, v)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges_list: seq<seq<int>>) returns (output: string)
  requires n <= |edges_list|
  requires forall k :: 0 <= k < |edges_list| ==> |edges_list[k]| >= 3 && edges_list[k][2] >= 1
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var row := edges_list[i];
    var l := row[0];
    var r := row[1];
    var d := row[2];
    var line: string;
    if l <= d && d <= r {
      line := IntToString((FloorDiv(r, d) + 1) * d);
    } else {
      line := IntToString(d);
    }
    lines := lines + [line];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
