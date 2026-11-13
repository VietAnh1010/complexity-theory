// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python sorts the characters and compares `z == s` before
//     scanning, O(n log n) as labelled; the Dafny only scans for the first
//     `s[i+1] < s[i]`, O(n), so the sort was dropped.
//
//   how this label could be wrong, and what to check:
//     The label comes from the Python's `z = sorted(s)`, compared with s
//     to decide NO. Check that the Dafny never sorts and decides by one
//     descent scan instead; it is O(n), a class below the labelled
//     program.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 25, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1155_A. Reverse a Substring  (problem 1577, solution 1577_61)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = input()
// s = [i for i in s]
// z = sorted(s)
// if z == s:
//     print("NO")
// else:
//     for i in range(n-1):
//         if ord(s[i]) > ord(s[i+1]):
//             print("YES")
//             print(i+1, i+2) 
//             break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
  requires n <= |s|
{
  var i := 0;
  var found := false;
  var idx := 0;
  while i < n - 1 && !found
    invariant 0 <= i
    decreases !found, n - 1 - i
  {
    if s[i+1] < s[i] {
      found := true;
      idx := i;
    } else {
      i := i + 1;
    }
  }
  if found {
    output := "YES\n" + IntToString(idx + 1) + " " + IntToString(idx + 2);
  } else {
    output := "NO";
  }
}
