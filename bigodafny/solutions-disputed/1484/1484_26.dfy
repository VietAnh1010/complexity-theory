// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over n numbers and calls StringLess(best, numbers[idx])
//     and StringLess(numbers[idx], worst) each iteration, each comparing
//     strings up to their shared prefix (up to m), so n strings each
//     scanned is O(n*m), not O(n). The Python max(l) and min(l) compare
//     strings the same way. StringLess is in the prelude and was not read,
//     hence medium.
//
//   how this label could be wrong, and what to check:
//     The label counts only the n phone numbers, but each comparison reads
//     the strings themselves. Check StringLess in the prelude: if it
//     compares character by character, each of the n iterations costs up
//     to the string length m, which is not constant by the naming rule.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 24, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 172_A. Phone Code  (problem 1484, solution 1484_26)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// l=[];i=0
// for _ in range(int(input())):l.append(input())
// a=max(l);b=min(l)
// while a[i]==b[i]:i+=1
// print(i)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<string>) returns (output: string)
  requires |numbers| == n
  requires n >= 1
{
  var best := numbers[0];
  var worst := numbers[0];
  var idx := 1;
  while idx < |numbers|
    decreases |numbers| - idx
  {
    if StringLess(best, numbers[idx]) { best := numbers[idx]; }
    if StringLess(numbers[idx], worst) { worst := numbers[idx]; }
    idx := idx + 1;
  }
  var i := 0;
  while i < |best| && i < |worst| && best[i] == worst[i]
    decreases |best| - i
  {
    i := i + 1;
  }
  output := IntToString(i);
}
