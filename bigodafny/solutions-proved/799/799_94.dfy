// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n+m)
//   cause          : both
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     The Dafny counts the heading into `counts` and decrements per letter
//     of the text, O(|s1| + |s2|); the Python scans and removes from the
//     list `a` per letter, O(|s1| * |s2|), so the translation replaced the
//     algorithm.
//
//   how this label could be wrong, and what to check:
//     The Python runs `k in a` and `a.remove(k)` on a list for each letter
//     of the second string, O(n*m) for two different strings, so `O(n**2)`
//     misnames it. The Dafny replaces the list with the map `counts`,
//     O(n+m). Check the Dafny's map decrement against the Python's
//     `a.remove(k)`.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 36, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 2,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": true, "set_build_in_loop":
//     false, "sorts": [], "uses_map": true, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 43_B. Letter  (problem 799, solution 799_94)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// a = list(input())
// 
// 
// b =(input())
// h=0
// 
// for k in b:
//     if k!=' ':
//         if k in a:
//             a.remove(k)
//         else:
//             print('NO')
//             h+=1
//             break
// 
// 
// if h==0:
//     print('YES')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(first_sentence: string, second_sentence: string) returns (output: string, ghost steps: nat)
  ensures steps <= 8 * |first_sentence| + 10 * |second_sentence| + 6
{
  steps := 1;
  var counts: map<char, int> := map[];
  var i := 0;
  while i < |first_sentence|
    invariant 0 <= i <= |first_sentence|
    invariant steps == 1 + 8 * i
    decreases |first_sentence| - i
  {
    var c := first_sentence[i];
    if c in counts {
      counts := counts[c := counts[c] + 1];
    } else {
      counts := counts[c := 1];
    }
    i := i + 1;
    steps := steps + 8;
  }
  var ans := "YES";
  var broke := false;
  i := 0;
  ghost var s0 := steps;
  while i < |second_sentence| && !broke
    invariant 0 <= i <= |second_sentence|
    invariant steps <= s0 + 10 * i
    decreases |second_sentence| - i
  {
    var c := second_sentence[i];
    if c != ' ' {
      if c in counts && counts[c] > 0 {
        counts := counts[c := counts[c] - 1];
      } else {
        ans := "NO";
        broke := true;
      }
    }
    i := i + 1;
    steps := steps + 10;
  }
  output := ans + "\n";
  steps := steps + 1;
}
