// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r4-d03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over the t test strings and for each runs `while i <
//     |s|` with step 2, appending one character in O(1), so t strings each
//     scanned once is O(n*m), not O(n**2). The Python prints s[i] over
//     range(0, len(s), 2) per test and pays the same, so the label names
//     the wrong sizes.
//
//   how this label could be wrong, and what to check:
//     The label squares one size, but the work is t strings, each scanned
//     once at stride 2. Check the loops: `while x < t` over the test
//     strings and `while i < |s|` inside it; nothing nests over the same
//     size.
//
//   structural facts (deterministic, from label_audit.py):
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
