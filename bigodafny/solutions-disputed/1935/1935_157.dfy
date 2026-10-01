// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-05
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny walks all |s| characters of the string in the while i <
//     |s| loop, appending to res, so it is O(n). The Python's two
//     s.replace calls and the input() read are also linear in the string
//     length, so the O(1) label names a cost no construct exhibits.
//
//   how this label could be wrong, and what to check:
//     The label assumes only arithmetic on n and k. Check the while i <
//     |s| loop in Solve, which visits every character of s, and the
//     Python's s.replace calls, which each scan the string.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 23, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1023_C. Bracket Subsequence  (problem 1935, solution 1935_157)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=map(int,input().split())
// ans=(n-k)//2
// s=input()
// s=s.replace("(","",ans)
// s=s.replace(")","",ans)
// print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, s: string) returns (output: string)
{
  var ans := FloorDiv(n - m, 2);
  var effAns := if ans < 0 then |s| else ans;
  var openRemoved := 0;
  var closeRemoved := 0;
  var res := "";
  var i := 0;
  while i < |s|
  {
    if s[i] == '(' && openRemoved < effAns {
      openRemoved := openRemoved + 1;
    } else if s[i] == ')' && closeRemoved < effAns {
      closeRemoved := closeRemoved + 1;
    } else {
      res := res + [s[i]];
    }
    i := i + 1;
  }
  output := res + "\n";
}
