// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-r3-05
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     Each of the O(n**2) inner iterations calls BitOr twice and BitOr
//     recurses on a/2 and b/2, costing O(log max a_i), so the Dafny is
//     O(n**2 log max a); the Python | operator is O(1) at these
//     magnitudes, so the translation introduced the extra factor.
//
//   how this label could be wrong, and what to check:
//     The label O(n**2) counts only the (l, r) pairs. Find the two BitOr
//     calls in the inner loop: BitOr recurses once per bit of its
//     arguments, adding a log of the element values per iteration. Then
//     compare the Python's s_a | ps[r], a constant-time machine OR for
//     values at most 10^9; if so the Python is O(n**2) and only the Dafny
//     pays the value term.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 41, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 2, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 631_A. Interview  (problem 1029, solution 1029_92)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// ps = list(map(int, input().split()))
// qs = list(map(int, input().split()))
// 
// maxi = 0
// s_a, s_b = 0, 0
// for l in range(n):
//     s_a = ps[l]
//     s_b = qs[l]
//     for r in range(l, n):
//         s_a = s_a | ps[r]
//         s_b = s_b | qs[r]
//         maxi = max(maxi, s_a + s_b)
// 
// print(maxi)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function BitOr(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures BitOr(a, b) >= 0
  decreases a + b
{
  if a == 0 then b
  else if b == 0 then a
  else 2 * BitOr(a / 2, b / 2) + (if a % 2 == 1 || b % 2 == 1 then 1 else 0)
}


method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
  requires n >= 0
  requires |a_list| == n
  requires |b_list| == n
  requires forall k :: 0 <= k < n ==> a_list[k] >= 0
  requires forall k :: 0 <= k < n ==> b_list[k] >= 0
{
  var maxi := 0;
  var l := 0;
  while l < n
    invariant 0 <= l <= n
    decreases n - l
  {
    var sa := a_list[l];
    var sb := b_list[l];
    var r := l;
    while r < n
      invariant l <= r <= n
      invariant sa >= 0 && sb >= 0
      decreases n - r
    {
      sa := BitOr(sa, a_list[r]);
      sb := BitOr(sb, b_list[r]);
      if sa + sb > maxi { maxi := sa + sb; }
      r := r + 1;
    }
    l := l + 1;
  }
  output := IntToString(maxi);
}
