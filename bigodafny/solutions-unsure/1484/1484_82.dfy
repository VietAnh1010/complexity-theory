// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(nlogn)
//   cause          : unclear
//   confidence     : low
//   auditor        : labelaudit-r4-s02
//
//   Which of the label or the translation is at fault was not determined
//   by the audit.
//
//   evidence:
//     SortStrings(numbers) is O(n log n) in the number of strings, but the
//     following prefix loop runs up to |first|, the string length, which
//     is a second size that the label omits. The Python's zip over
//     numbers[0] and numbers[-1] pays the same string-length term.
//
//   how this label could be wrong, and what to check:
//     The label O(nlogn) names only the string count. Check the while loop
//     bound `i < |first| && i < |last|`: its length is the width of a
//     phone number (statement says 1 to 20), a separate size from n. If
//     width counts as a size the class is O(nlogn+m) (outside the
//     vocabulary, `other`); if a statement cap of 20 is treated as
//     constant, which the naming rule says it should not be, O(nlogn)
//     stands.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 19, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": ["SortStrings"], "uses_map":
//     false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 172_A. Phone Code  (problem 1484, solution 1484_82)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// cases = int(input())
// 
// numbers = []
// while cases:
//     cases -= 1
//     s = input()
//     numbers.append(s)
// 
// numbers.sort()
// 
// ct = 0
// 
// for i, j in zip(numbers[0], numbers[-1]):
//     if i == j:
//         ct += 1
//     else:
//         print(ct)
//         break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<string>) returns (output: string)
  requires |numbers| == n
  requires n >= 1
{
  var sorted := SortStrings(numbers);
  var first := sorted[0];
  var last := sorted[|sorted|-1];
  var ct := 0;
  var i := 0;
  while i < |first| && i < |last| && first[i] == last[i]
    decreases |first| - i
  {
    ct := ct + 1;
    i := i + 1;
  }
  output := IntToString(ct);
}
