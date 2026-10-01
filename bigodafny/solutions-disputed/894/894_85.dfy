// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r3d-02
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python calls Valid for each i, and each call loops i times
//     (recomputing the prefix and sum(l)), which is O(n**2) as labelled.
//     The Dafny hoists sum into `total` and keeps a running prefix s in
//     one loop over a_list, which is O(n): the algorithm was replaced by a
//     faster single pass.
//
//   how this label could be wrong, and what to check:
//     The label comes from the Python's `for i in range(len(l))` calling
//     Valid(l, i, x, y), which re-sums a prefix of length i each time (and
//     sum(l) inside the check). Check that the Dafny computes `total` once
//     and a running prefix `s` in a single loop with no nested pass.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 30, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 357_A. Group of Students  (problem 894, solution 894_85)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// dumb = input()
// l = [int(o) for o in input().split()]
// x, y = [int(o) for o in input().split()]
// 
// def Valid(l, k, x, y):
//     s = 0
//     for i in range(k):
//         s += l[i]
//         if s >= x and s <= y and sum(l) - s >= x and sum(l) - s <= y and s != sum(l) and s != 0 and sum(l) - s != 0:
//             return True
//     return False
// 
// for i in range(len(l)):
//     if Valid(l, i, x, y):
//         break
// if i+1 > 0 and i < len(l) and Valid(l, i, x, y):
//     print(i+1)
// else:
//     print(0)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, x: int, y: int) returns (output: string)
{
  var total := 0;
  var idx := 0;
  while idx < |a_list|
    decreases |a_list| - idx
  {
    total := total + a_list[idx];
    idx := idx + 1;
  }
  var s := 0;
  var p := 0;
  var found := false;
  while p < |a_list| && !found
    decreases |a_list| - p
  {
    s := s + a_list[p];
    if s >= x && s <= y && (total - s) >= x && (total - s) <= y && s != total && s != 0 && (total - s) != 0 {
      found := true;
    }
    p := p + 1;
  }
  if found {
    output := IntToString(p + 1) + "\n";
  } else {
    output := "0\n";
  }
}
