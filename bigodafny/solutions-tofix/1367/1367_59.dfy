// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-08
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     Every iteration of the while loop unconditionally does `di := di[k
//     := iv]`, an O(|di|) full-map-copy write per the dataset's map rule,
//     and |di| grows up to n, giving O(n**2) total across the n-length
//     loop; Python's `di[k]=i` dict assignment is O(1) amortised, so
//     Python is genuinely O(n) as labelled.
//
//   how this label could be wrong, and what to check:
//     The label assumes map `di` behaves like Python's dict with O(1)
//     writes. Check the loop body: `di := di[k := iv]` executes
//     unconditionally on every one of the n iterations, and per the
//     map-write rule this is O(|di|) per call, so confirm this alone gives
//     O(n**2); also check whether `di := di - {iv}` (map key removal) adds
//     a second O(|di|) cost on top.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 23, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": true,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 889_A. Petya and Catacombs  (problem 1367, solution 1367_59)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// di = {0 : 0}
// k = 1
// q = 1
// for i in a:
//     if i in di:
//         del di[i]
//     else:
//         q += 1
//     di[k] = i
//     k += 1
// print(q)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<int>) returns (output: string)
{
  var di: map<int, int> := map[0 := 0];
  var k := 1;
  var q := 1;
  var idx := 0;
  while idx < |coordinates|
    decreases |coordinates| - idx
  {
    var iv := coordinates[idx];
    if iv in di {
      di := di - {iv};
    } else {
      q := q + 1;
    }
    di := di[k := iv];
    k := k + 1;
    idx := idx + 1;
  }
  output := IntToString(q);
}
