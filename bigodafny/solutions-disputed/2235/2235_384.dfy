// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-s03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over the t strings of s_list and the inner while loop
//     walks every character of each s (j < |s|) to copy every second one,
//     so the cost is n strings each scanned once, O(n*m), not O(n). The
//     Python's a[::2] on each test string is also linear in its length, so
//     the label is wrong for both.
//
//   how this label could be wrong, and what to check:
//     The label O(n) counts only the test cases, but each test's string
//     has its own length 2n-1. Open the inner `while j < |s|` loop and
//     check that it runs per character; if the string length is treated as
//     a constant the label stands (the statement caps n at 50, which is
//     not a source literal), otherwise it should be O(n*m). The n_list
//     argument is unused.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 26, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 2, "loops":
//     2, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1400_A. String Similarity  (problem 2235, solution 2235_384)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #872
// for _ in range(int(input())):
//     n=int(input())
//     a=input()
//     print(a[::2])
//         
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(t: int, n_list: seq<int>, s_list: seq<string>) returns (output: string)
  requires t <= |s_list|
{
  var lines: seq<string> := [];
  var i := 0;
  while i < t
    invariant 0 <= i
    decreases t - i
  {
    var s := s_list[i];
    var res: seq<char> := [];
    var j := 0;
    while j < |s|
      invariant 0 <= j <= |s|
      decreases |s| - j
    {
      if j % 2 == 0 { res := res + [s[j]]; }
      j := j + 1;
    }
    lines := lines + [res];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
