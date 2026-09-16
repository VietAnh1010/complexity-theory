// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The inner while loops over i and j are hardcoded to 2 iterations
//     each (`i < 2`, `j < 2`), never scanning a variable-width row, so
//     there is no m dimension in either the Dafny or Python (`for i in
//     range(2): for j in range(2)`); the true class is O(n), and the
//     labelled O(n*m) is a label error.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 36, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 3, "loops":
//     3, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1351_B. Square?  (problem 1018, solution 1018_421)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #By maxwill, contest: Testing Round #16 (Unrated), problem: (B) Square?, Compilation error, #, Copy
// T = int(input().strip())
// for i in range(T):
//     a = list(map(int, input().strip().split()))
//     b = list(map(int, input().strip().split()))
//     flag = False
//     for i in range(2):
//         for j in range(2):
//             if(a[i] == b[j] and a[1-i]+b[1-j] == a[i]):
//                 flag = True
//     
//     print("Yes" if flag else "No" ) 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string)
  requires n >= 0
  requires |edges| == 2 * n
  requires forall k :: 0 <= k < |edges| ==> |edges[k]| == 2
{
  var lines: seq<string> := [];
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    decreases n - t
  {
    var a := edges[2 * t];
    var b := edges[2 * t + 1];
    var flag := false;
    var i := 0;
    while i < 2
      decreases 2 - i
    {
      var j := 0;
      while j < 2
        decreases 2 - j
      {
        if a[i] == b[j] && a[1 - i] + b[1 - j] == a[i] {
          flag := true;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    lines := lines + [if flag then "Yes" else "No"];
    t := t + 1;
  }
  output := Join(lines, "\n");
}
