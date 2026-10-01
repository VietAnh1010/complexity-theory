// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-s05
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve runs one loop on c, comparing a[c] and b[c] and exiting at the
//     first difference or at min(|a|,|b|), so it pays one length, O(n);
//     the Python lowers both strings fully, but with equal-size strings
//     that is 2n, still O(n), so n+m names a size that does not vary
//     independently.
//
//   how this label could be wrong, and what to check:
//     The label O(n+m) assumes two independent string lengths, but the
//     problem says the two strings have the same size, so n and m are one
//     size. Open the statement and confirm the sentence 'two strings of
//     the same size'; also note the Dafny is a single lockstep loop over c
//     bounded by min(|a|,|b|), not one pass over each. If the Python's two
//     .lower() calls count as separate passes you may prefer to keep
//     O(n+m) as a harness cost.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 28, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 112_A. Petya and Strings  (problem 3060, solution 3060_1359)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a=input().lower()
// b=input().lower()
// c=0
// while True:
//  try:
//   if a[c]==b[c]:
//    c+=1
//   else:
//    if a[c]<b[c]:
//     print(-1)
//     break
//    else:
//     print(1)
//     break
//  except IndexError:
//   print(0)
//   break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s1: string, s2: string) returns (output: string)
{
  var a := s1;
  var b := s2;
  var c := 0;
  while true
    invariant 0 <= c
    decreases |a| - c
  {
    if c >= |a| || c >= |b| {
      output := "0";
      return;
    }
    var ca: char := if a[c] >= 'A' && a[c] <= 'Z' then ((a[c] as int) + 32) as char else a[c];
    var cb: char := if b[c] >= 'A' && b[c] <= 'Z' then ((b[c] as int) + 32) as char else b[c];
    if ca == cb {
      c := c + 1;
    } else if ca < cb {
      output := "-1";
      return;
    } else {
      output := "1";
      return;
    }
  }
}
