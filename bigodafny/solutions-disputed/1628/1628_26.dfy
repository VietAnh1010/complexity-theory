// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(nlogn)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     `Norm1628a` splits s in half, recurses on both halves, then calls
//     `StringLess` and concatenates, O(|s|) per level over log n levels,
//     O(n log n); the Python's `sm` has the same recursion with `s1 < s2`
//     and `s1 + s2`.
//
//   how this label could be wrong, and what to check:
//     The label is constant, but `sm` recurses on both halves and then
//     compares and concatenates the halves, T(n) = 2T(n/2) + O(n). Check
//     the even-length case of `Norm1628a`: `StringLess(a, b)` and `a + b`
//     each cost O(|s|), so the class is O(n log n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 24, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 0, "loops": 0,
//     "recursive_helpers": 1, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 560_D. Equivalent Strings  (problem 1628, solution 1628_26)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def sm(s):
//     if len(s) % 2 == 1:
//         return s
//     s1 = sm(s[:len(s) // 2])
//     s2 = sm(s[len(s) // 2:])
//     if s1 < s2:
//         return s1 + s2
//     else:
//         return s2 + s1
//     
// if sm(input()) == sm(input()):
//     print("YES")
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s1: string, s2: string) returns (output: string)
  requires |s1| > 0 && |s2| > 0
{
  var n1 := Norm1628a(s1);
  var n2 := Norm1628a(s2);
  if n1 == n2 {
    output := "YES";
  } else {
    output := "NO";
  }
}

function Norm1628a(s: string): string
  requires |s| > 0
  decreases |s|
{
  if |s| % 2 == 1 then s
  else
    var half := |s| / 2;
    var a := Norm1628a(s[..half]);
    var b := Norm1628a(s[half..]);
    if StringLess(a, b) then a + b else b + a
}
