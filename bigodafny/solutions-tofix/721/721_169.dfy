// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop over numbers calls Repeat("9",cnt9) and Repeat("8",cnt8),
//     each costing O(length) per the table, so total cost is linear in the
//     summed test values with no nested or squared construct; the Python's
//     `['9']*(n-...) + ['8']*...` list construction is the same linear
//     build, so O(n**2) matches neither source.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 24, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join", "Repeat"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1388_B. Captain Flint and a Long Voyage  (problem 721, solution 721_169)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import ceil
// t = int(input())
// for _ in range(t):
//     n = int(input())
//     s = []
//     if n == 1:
//         print(8)
//     else:
//         s = ['9'] * (n - int(ceil(n / 4)))
//         s += ['8'] * int(ceil(n / 4))
//     print(''.join(s))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n && i < |numbers|
    invariant 0 <= i
    decreases n - i
  {
    var nv := numbers[i];
    if nv == 1 {
      parts := parts + ["8\n" + "\n"];
    } else if nv > 0 {
      var cnt8 := (nv + 3) / 4;
      var cnt9 := nv - cnt8;
      parts := parts + [Repeat("9", cnt9) + Repeat("8", cnt8) + "\n"];
    } else {
      parts := parts + ["\n"];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}
