// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-13
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loop iterates i from 0 to |s| once, doing O(1) work per
//     character, so its cost is O(n) in the string length, and Python's
//     two str.replace calls each scan the whole string too, so the O(1)
//     label undercounts both the Python and the Dafny.
//
//   how this label could be wrong, and what to check:
//     The label claims constant time. Confirm the Dafny 'while i<|s|' loop
//     scans every character of s regardless of 'ans', and that Python's
//     two s.replace(...) calls likewise scan the full string each time; if
//     both are proportional to |s|, the O(1) label is wrong regardless of
//     any translation choice.
//
//   structural facts (deterministic, from labelaudit.py):
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
