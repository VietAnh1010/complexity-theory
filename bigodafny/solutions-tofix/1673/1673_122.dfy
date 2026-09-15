// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-11
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny while loop reads only pairs[i][0] per iteration and builds
//     pieces with seq+[x] with no pieces[k] read in the loop, so appends
//     are O(1) amortised and the whole method is O(n), matching the
//     Python's single a=... read per line.
//
//   how this label could be wrong, and what to check:
//     The label implies a second scanned dimension m from pairs[k].
//     Confirm the description's ai/gi pair format gives each row exactly
//     one used field pairs[i][0]; if so there is no m and the loop, in
//     both Python (a=int(input().split()[0])) and Dafny, is O(n).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 25, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 1, "loops":
//     1, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 282_B. Painting Eggs  (problem 1673, solution 1673_122)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// eggs=int(input())
// diff=0
// c=['A' for i in range(eggs)]
// for i in range(eggs):
//     a=int(input().split()[0])
// 
//     if a+diff<501:
//         diff+=a
//     else:
//         c[i]='G'
//         
//         diff-=1000-a
// print(''.join(c))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
  requires n <= |pairs|
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 1
{
  var diff := 0;
  var pieces: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i
    decreases n - i
  {
    var a := pairs[i][0];
    if a + diff < 501 {
      diff := diff + a;
      pieces := pieces + ["A"];
    } else {
      diff := diff - (1000 - a);
      pieces := pieces + ["G"];
    }
    i := i + 1;
  }
  output := Join(pieces, "");
}
