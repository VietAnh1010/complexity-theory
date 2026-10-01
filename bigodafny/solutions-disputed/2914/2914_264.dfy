// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-08
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop `while i < n && !found` reads only intervals[i][0] and
//     intervals[i][1], so it is O(n) with no walk of a row. The Python
//     parses each line into exactly two ints and indexes mas[i][0] and
//     mas[i][1], so it is O(n) too and the O(n*m) label is wrong.
//
//   how this label could be wrong, and what to check:
//     The label assumes chapter rows have a variable width m. Check the
//     statement: each of the n lines holds exactly two integers l_i and
//     r_i, so row width is a constant; if rows could be longer the label
//     would stand.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 22, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1136_A. Nastya Is Reading a Book  (problem 2914, solution 2914_264)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// mas =  []
// 
// for i in range(n):
//     c = list(map(int,input().split()))
//     mas.append(c)
// 
// k = int(input())
// 
// for i in range(n):
//     if k >= mas[i][0] and k <= mas[i][1]:
//         print(n-i)
//         break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, intervals: seq<seq<int>>, value: int) returns (output: string)
{
  output := "";
  var i := 0;
  var found := false;
  while i < n && !found
    invariant 0 <= i
    decreases if found then 0 else n - i
  {
    if i < |intervals| && |intervals[i]| >= 2 {
      var lo := intervals[i][0];
      var hi := intervals[i][1];
      if value >= lo && value <= hi {
        output := IntToString(n - i);
        found := true;
      }
    }
    i := i + 1;
  }
}
