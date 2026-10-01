// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-05
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loops i < n once, reading only pairs[i][0] and appending
//     to pieces in O(1), then calls Join(pieces, "") once at O(n). The
//     Python does one range(eggs) loop splitting a two-token line and a
//     single ''.join, so both are O(n) and no m dimension is scanned.
//
//   how this label could be wrong, and what to check:
//     The label assumes a second dimension m. Check the statement: each of
//     the n lines contains exactly two integers ai and gi, so there is no
//     variable width; if lines could carry many values the label might
//     stand.
//
//   structural facts (deterministic, from label_audit.py):
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
