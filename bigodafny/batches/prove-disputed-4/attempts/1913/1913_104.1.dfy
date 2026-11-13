// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python's first line after input is `ss = sorted(s)`, an O(n log
//     n) sort whose result is never read; the Dafny drops it and keeps
//     only the backward loop over s, O(n).
//
//   how this label could be wrong, and what to check:
//     The Python computes `ss = sorted(s)` and never uses it, but the sort
//     still runs and is what the O(n log n) label measured. Check that the
//     Dafny omits it: the remaining backward scan is O(n). Restoring the
//     sort, unused, would restore the label.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 21, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["JoinInts"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1043_C. Smallest Word  (problem 1913, solution 1913_104)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = input()
// ss = sorted(s)
// r = [0] * len(s)
// b_char = 'b'
// for i, c in enumerate(reversed(s)):
//     if c != b_char:
//         r[len(s)-i-1] = 1
//         b_char = 'a' if b_char == 'b' else 'b'
// print(" ".join([str(i) for i in r]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 10 * |s| + 10 + |output|
{
  var n := |s|;
  steps := 2 + n;
  var r := seq(n, _ => 0);
  var bChar := 'b';
  var idx := n - 1;
  while idx >= 0
    invariant -1 <= idx < n
    invariant |r| == n
    invariant steps == 2 + n + 10 * (n - 1 - idx)
    decreases idx + 1
  {
    if s[idx] != bChar {
      r := r[idx := 1];
      bChar := if bChar == 'b' then 'a' else 'b';
    }
    idx := idx - 1;
    steps := steps + 10;
  }
  output := JoinInts(r, " ");
  JoinIntsLen(r, " ");
  steps := steps + SumDigits(r) + |r|;
}
