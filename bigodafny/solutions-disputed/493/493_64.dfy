// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-04
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The while loop scans the entire string_ to find hasC and lastF, an
//     O(n) pass equivalent to Python's s.index('C') and s.rindex('F'),
//     which are themselves O(n) scans; O(1) is wrong for both the Dafny
//     and the Python.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 28, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// p03957 CODE FESTIVAL 2016 qual C - CF  (problem 493, solution 493_64)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = input()
// if 'C' in s and 'F' in s and s.index('C') < s.rindex('F'):
//     print('Yes')
// else:
//     print('No')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(string_: string) returns (output: string)
{
  var hasC := false;
  var hasF := false;
  var firstC := 0;
  var lastF := 0;
  var i := 0;
  while i < |string_|
    decreases |string_| - i
  {
    if string_[i] == 'C' && !hasC {
      hasC := true;
      firstC := i;
    }
    if string_[i] == 'F' {
      hasF := true;
      lastF := i;
    }
    i := i + 1;
  }
  if hasC && hasF && firstC < lastF {
    output := "Yes\n";
  } else {
    output := "No\n";
  }
}
