// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : harness
//   confidence     : high
//   auditor        : labelaudit-batch-07
//
//   Which of the label or the translation is at fault was not determined
//   by the audit.
//
//   evidence:
//     The Dafny Solve only reads row[0] and row[2] from each grid row
//     inside the while loop and never walks the row, so it is O(n);
//     Python's L=list(map(int,input().split())) additionally pays to parse
//     each full line, which is outside what Solve measures, so O(n*m) is
//     right about the harness, not the method.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 21, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1108_A. Two distinct points  (problem 936, solution 936_203)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// for a in range(n):
//     L=list(map(int,input().split()))
//     if(L[0]==L[2]):
//         print(L[0],L[2]+1)
//     else:
//         print(L[0],L[2])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, grid: seq<seq<int>>) returns (output: string)
  requires forall r :: r in grid ==> |r| >= 3
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n && i < |grid|
    invariant 0 <= i
    decreases n - i
  {
    var row := grid[i];
    if row[0] == row[2] {
      parts := parts + [IntToString(row[0]) + " " + IntToString(row[2] + 1) + "\n"];
    } else {
      parts := parts + [IntToString(row[0]) + " " + IntToString(row[2]) + "\n"];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}
