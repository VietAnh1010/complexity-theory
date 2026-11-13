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
//     The Dafny loops over `values`, which always holds the four horseshoe
//     colours, inserting each into the map `dic`, so the work is a fixed
//     four iterations, O(1); the Python's dict loop is the same.
//
//   how this label could be wrong, and what to check:
//     The label treats the input as a growing list, but it is always
//     exactly four horseshoe colours on one line. Check the input format;
//     a fixed four values make the dict loop constant and the class O(1).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 19, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": true,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 228_A. Is your horseshoe on the other hoof?  (problem 1434, solution 1434_1729)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x = list(map(int, input().split()))
// dic ={}
// for each in x:
//     if each not in dic:
//         dic[each] = 0
//     dic[each] += 0
// h = len(dic)
// print(4 - h)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(values: seq<int>) returns (output: string)
{
  var dic: map<int, int> := map[];
  var i := 0;
  while i < |values|
    decreases |values| - i
  {
    var each := values[i];
    if each !in dic {
      dic := dic[each := 0];
    }
    dic := dic[each := dic[each] + 0];
    i := i + 1;
  }
  var h := |dic|;
  output := IntToString(4 - h);
}
