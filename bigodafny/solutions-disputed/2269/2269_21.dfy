// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The outer loop over i (n values) and inner loop over j (up to i - r
//     values) each call IsPalindrome269(s[j..i]), whose recursion
//     IsPalindromeFrom269 has depth about |t|/2; on an all-equal string
//     nothing breaks early, so the cost is cubic, O(n**3). The Python's `t
//     != t[::-1]` is likewise linear per pair, so the label is wrong for
//     both.
//
//   how this label could be wrong, and what to check:
//     The label assumes quadratic work, but each of the O(n**2) (i, j)
//     pairs builds and palindrome-tests a substring costing up to its
//     length. Take s = 'qqqqqqqq' (all palindromes) and count the work:
//     the Python's t[::-1] compare and the Dafny's IsPalindromeFrom269
//     both do about (i-j)/2 steps per pair, giving a cubic total.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 43, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 981_A. Antipalindrome  (problem 2269, solution 2269_21)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s, r = input(), 0
// i = len(s)
// while i > r:
//     for j in range(i - r):
//         t = s[j:i]
//         if t != t[::-1]:
//             r = i - j
//             break
//     i -= 1
// print(r)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  var r := 0;
  var i := |s|;
  while i > r
    invariant 0 <= r
    invariant 0 <= i <= |s|
    decreases i
  {
    var j := 0;
    var found := false;
    while j < i - r && !found
      invariant 0 <= j
      invariant 0 <= r
      invariant 0 <= i <= |s|
      decreases (i - r) - j
    {
      var t := s[j..i];
      if !IsPalindrome269(t) {
        r := i - j;
        found := true;
      }
      j := j + 1;
    }
    i := i - 1;
  }
  output := IntToString(r);
}

function IsPalindrome269(t: string): bool
{
  IsPalindromeFrom269(t, 0, |t| - 1)
}

function IsPalindromeFrom269(t: string, lo: int, hi: int): bool
  requires 0 <= lo
  requires hi < |t|
  decreases hi - lo
{
  if lo >= hi then true
  else if t[lo] != t[hi] then false
  else IsPalindromeFrom269(t, lo + 1, hi - 1)
}
