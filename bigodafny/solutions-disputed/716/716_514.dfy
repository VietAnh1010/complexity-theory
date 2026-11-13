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
//     Both the Python's loop over `verts` and the Dafny's loop over
//     `edges` read only the first two numbers of each of n rows, which are
//     fixed pairs, so the cost is O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes row width varies. Each point is an (x, y) pair,
//     the Dafny requires `|edges[k]| == 2`, and both programs read only
//     `v[0] + v[1]`. Check the input format: two numbers per line makes m
//     a constant and the class O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 16, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1047_B. Cover Points  (problem 716, solution 716_514)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// d = int(input())
// 
// verts = []
// 
// for i in range(d):
//     d = [int(x) for x in input().split(' ')]
//     verts.append(d)
// 
// maxx = 0
// for v in verts:
//     maxx = max(maxx, v[0] + v[1])
// 
// print(maxx)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string)
  requires forall k :: 0 <= k < |edges| ==> |edges[k]| == 2
{
  var c := 0;
  var i := 0;
  while i < |edges|
    decreases |edges| - i
  {
    var s := edges[i][0] + edges[i][1];
    if s > c { c := s; }
    i := i + 1;
  }
  output := IntToString(c);
}
