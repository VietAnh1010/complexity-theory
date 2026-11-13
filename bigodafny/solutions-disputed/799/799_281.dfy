// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n+m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny counts characters of `first_sentence` into a map in one
//     pass and consumes `second_sentence` in a second pass, O(|s1| +
//     |s2|), as the Python's two dict loops do.
//
//   how this label could be wrong, and what to check:
//     The label names one size, but the code reads two independent
//     strings, the heading and the letter, one pass each. Check that both
//     inputs vary in length independently; then the class is O(n+m) by the
//     naming rule.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 43, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 2,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": true, "set_build_in_loop":
//     false, "sorts": [], "uses_map": true, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 43_B. Letter  (problem 799, solution 799_281)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a={}
// for c in input():
//     if c==" ":
//         continue
//     if c in a:
//         a[c]+=1
//     else:
//         a[c]=1
// ans="YES"
// for c in input():
//     if c==" ":
//         continue
//     if c in a:
//         if a[c]==0:
//             ans="NO"
//             break
//         else:
//             a[c]-=1
//     else:
//         ans="NO"
//         break
// print(ans)
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(first_sentence: string, second_sentence: string) returns (output: string)
{
  var counts: map<char, int> := map[];
  var i := 0;
  while i < |first_sentence|
    decreases |first_sentence| - i
  {
    var c := first_sentence[i];
    if c != ' ' {
      if c in counts {
        counts := counts[c := counts[c] + 1];
      } else {
        counts := counts[c := 1];
      }
    }
    i := i + 1;
  }
  var ans := "YES";
  var broke := false;
  i := 0;
  while i < |second_sentence| && !broke
    decreases |second_sentence| - i
  {
    var c := second_sentence[i];
    if c != ' ' {
      if c in counts {
        if counts[c] == 0 {
          ans := "NO";
          broke := true;
        } else {
          counts := counts[c := counts[c] - 1];
        }
      } else {
        ans := "NO";
        broke := true;
      }
    }
    i := i + 1;
  }
  output := ans + "\n";
}
