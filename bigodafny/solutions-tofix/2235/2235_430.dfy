// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-17
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The inner while loop appends buf := buf + [s[i]] stepping i by 2,
//     reading only the input string s[i], never buf itself, so each append
//     is O(1) and the total per test case is O(|s|); summed over t test
//     cases this is O(n), and the Python's equivalent stride-2 print loop
//     is likewise linear.
//
//   how this label could be wrong, and what to check:
//     The label implies a quadratic construct, but buf := buf + [s[i]]
//     never reads buf[i] in the same loop (only s[i], the input) so per
//     the table it is the O(1)-per-append deferred-concat case, not the
//     O(|s|) flatten case. Confirm no other loop reads buf by index before
//     the loop ends, and check the Python's for-i-in-range(0,len(s),2)
//     print loop is also single-pass linear.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 34, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 2, "loops":
//     2, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1400_A. String Similarity  (problem 2235, solution 2235_430)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #Written by Shagoto
// 
// t = int(input())
// for x in range(t):
//     n = int(input())
//     s = input()
//     
//     if(n == 1):
//         print(s)
//     
//     else:
//         for i in range(0, len(s), 2):
//             print(s[i], end = "")
//         print()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(t: int, n_list: seq<int>, s_list: seq<string>) returns (output: string)
  requires t <= |n_list|
  requires t <= |s_list|
{
  var parts: seq<string> := [];
  var x := 0;
  while x < t
    invariant 0 <= x
    decreases t - x
  {
    var n := n_list[x];
    var s := s_list[x];
    var line: string;
    if n == 1 {
      line := s;
    } else {
      var buf: string := "";
      var i := 0;
      while i < |s|
        invariant 0 <= i
        decreases |s| - i
      {
        buf := buf + [s[i]];
        i := i + 2;
      }
      line := buf;
    }
    parts := parts + [line];
    x := x + 1;
  }
  output := Join(parts, "\n");
}
