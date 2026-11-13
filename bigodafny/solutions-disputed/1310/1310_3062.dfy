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
//     Both programs loop over the n stations reading only the first two
//     numbers of each row to update the passenger count, so the cost is
//     O(n); a station row is a fixed pair.
//
//   how this label could be wrong, and what to check:
//     The label assumes row width varies. Each station line is the pair
//     (a, b) and both programs read only `s[i][0]` and `s[i][1]`. Check
//     the input format; two numbers per line make m a constant and the
//     class O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 22, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 116_A. Tram  (problem 1310, solution 1310_3062)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// x = list(map(int, input().split()))
// s = []
// for i in range(0,x[0]):
//     s.append(list(map(int, input().split())))
// q = 1
// p = 0
// q = 0
// for i in range(0,x[0]):
//     p = p - s[i][0] + s[i][1]
//     if p > q :
//         q = p
// print(q)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string)
  requires n <= |edges|
  requires forall k :: 0 <= k < |edges| ==> |edges[k]| >= 2
{
{

  var people := 0;
  var maxPeople := 0;
  var i := 0;
  while i < n
    decreases n - i
  {
    var aa := edges[i][0];
    var bb := edges[i][1];
    people := people + bb - aa;
    if people > maxPeople { maxPeople := people; }
    i := i + 1;
  }
  output := IntToString(maxPeople);
}
}
