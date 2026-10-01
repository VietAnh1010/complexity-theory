// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve calls the recursive Repeat with counts z+2w and x-w, costing
//     O(n) in the VALUE n (about n/7 characters, up to 10^6), and the
//     Python's string repetition builds the same long output, so O(1) is
//     wrong.
//
//   how this label could be wrong, and what to check:
//     The label assumes straight-line code, but the output string has
//     length about n/7 digits. Check Repeat('4', ...) and Repeat('7', x-w)
//     in Solve (recursion depth equals the count) and the Python's
//     '4'*(...) + '7'*(...), which also builds a length-O(n) string.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 19, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Repeat"], "loop_depth": 0, "loops":
//     0, "recursive_helpers": 1, "seq_append_read_in_same_loop": false,
//     "seq_args": 0, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 110_C. Lucky Sum of Digits  (problem 271, solution 271_51)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// x,y=n//7,n%7
// z,w=y//4,y%4
// if(x<w):
//     print(-1)
// else:
//     print('4'*(z+w*2)+'7'*(x-w))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var x := n / 7;
  var y := n % 7;
  var z := y / 4;
  var w := y % 4;
  if x < w {
    output := "-1";
  } else {
    output := Repeat('4', z + w * 2) + Repeat('7', x - w);
  }
}

function Repeat(c: char, n: int): string
  decreases if n < 0 then 0 else n
{
  if n <= 0 then "" else [c] + Repeat(c, n - 1)
}
