// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     ParseInts(c_list) and the single loop over |v| are both linear in
//     the one list, and k only decreases by at most 8 per step so it adds
//     no cost term; the Python enumerates one list likewise, so no m
//     dimension exists.
//
//   how this label could be wrong, and what to check:
//     The label O(n+m) assumes a second dimension m, but the only
//     collection is c_list; the other input k (b) is a scalar that is
//     subtracted from, never looped to. Check that the loop `while i <
//     |v|` is the only loop and that k does not bound any iteration.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 25, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "ParseInts"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 839_A. Arya and Bran  (problem 2019, solution 2019_392)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// _, k = map(int, input().split())
// 
// acc = 0
// result = -1
// for i, v in enumerate(map(int, input().split())):
//     acc += v
//     d = min(acc, 8) 
//     k -= d
//     acc -= d
//     if k <= 0:
//         result = i + 1
//         break
// 
// print(result)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<string>) returns (output: string)
{
  var k := b;
  var v := ParseInts(c_list);
  var acc := 0;
  var result := -1;
  var i := 0;
  var stopped := false;
  while i < |v| && !stopped
    decreases |v| - i
  {
    acc := acc + v[i];
    var d := if acc < 8 then acc else 8;
    k := k - d;
    acc := acc - d;
    if k <= 0 {
      result := i + 1;
      stopped := true;
    }
    i := i + 1;
  }
  output := IntToString(result);
}
