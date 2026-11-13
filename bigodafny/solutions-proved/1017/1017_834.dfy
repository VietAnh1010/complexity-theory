// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(1)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny reads only `s[6]` and tests its parity, straight-line
//     O(1); the Python copies s into a list first, but s always has seven
//     characters, so that loop is constant too.
//
//   how this label could be wrong, and what to check:
//     The label treats the input string as a growing size, but it is
//     always exactly seven characters ('A' plus six hex digits; the Dafny
//     requires `|s| == 7`). Check the problem's input format; a fixed
//     length makes the Python's copy loop constant and the class O(1).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 12, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 0, "loops": 0,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1331_D. Again?  (problem 1017, solution 1017_834)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import random
// 
// s = input()
// a = list()
// for items in s:
//     a.append(items)
// 
// if int(a[6])%2 == 0:
//    print('0')
// else:
//    print('1')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string, ghost steps: nat)
  requires |s| == 7
  ensures steps <= 6
{
  steps := 4;
  var d := s[6] as int - '0' as int;
  if d % 2 == 0 {
    output := "0";
    steps := steps + 1;
  } else {
    output := "1";
    steps := steps + 1;
  }
}
