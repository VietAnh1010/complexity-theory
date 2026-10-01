// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r4-d02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve has a single `while i < n` loop that reads s[i] and updates
//     diff, ans and f in O(1) per step, with no nested loop or recursion,
//     so it is O(n). The Python fn() likewise runs one `for i in range(n)`
//     pass, so the O(n**2) label is wrong for both.
//
//   how this label could be wrong, and what to check:
//     The label claims quadratic work, but the body may be a single pass.
//     Open Solve and count the loops: if the only loop is `while i < n`
//     over s with O(1) body work, the row is linear and the label is
//     wrong.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 39, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1322_A. Unusual Competitions  (problem 1168, solution 1168_57)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def fn():
//     diff = 0
//     ans = 0
//     f = 'p'
//     n = int(input())
//     s = input()
//     if len(s) % 2 == 1:
//         return -1
// 
//     for i in range(n):
//         if s[i] == '(': diff += 1
//         elif s[i] == ')': diff -= 1
// 
//         if diff >= 0:
//             f = 'p'
//             continue
// 
//         elif diff < 0:
//             ans += 1
//             if f == 'p':
//                 f = 'n'
//                 ans +=1
//     if diff == 0:
//         return ans
//     else:
//         return -1
// 
// print(fn())
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
  requires n == |s|
{
  if |s| % 2 == 1 {
    output := "-1";
  } else {
    var diff := 0;
    var ans := 0;
    var f := 'p';
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      decreases n - i
    {
      if s[i] == '(' {
        diff := diff + 1;
      } else if s[i] == ')' {
        diff := diff - 1;
      }
      if diff >= 0 {
        f := 'p';
      } else {
        ans := ans + 1;
        if f == 'p' {
          f := 'n';
          ans := ans + 1;
        }
      }
      i := i + 1;
    }
    if diff == 0 {
      output := IntToString(ans);
    } else {
      output := "-1";
    }
  }
}
