// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny's `while i < n - 1 && !found` loop scans s for a descent
//     and runs n - 1 times on a sorted string, O(n); the Python's
//     `next(...)` generator performs the same scan.
//
//   how this label could be wrong, and what to check:
//     The label is constant, but the Python's generator `next(i for i in
//     range(n - 1) if s[i] > s[i + 1])` scans until the first descent, the
//     whole string when s is sorted. Check with a non-decreasing s: both
//     programs read all n characters, so the class is O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 25, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1155_A. Reverse a Substring  (problem 1577, solution 1577_411)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def main():
//     n = int(input())
//     s = input()
// 
//     try:
//         index = next(i for i in range(n - 1) if s[i] > s[i + 1])
//         print('YES\n%d %d' % (index + 1, index + 2))
//     except StopIteration:
//         print('NO')
// 
// 
// if __name__ == '__main__':
//     main()
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
