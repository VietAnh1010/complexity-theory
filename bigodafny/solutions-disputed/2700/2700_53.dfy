// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(1)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve has no loops: it makes four ParseInt calls on one-character
//     slices and a few IntToString calls (charged 1), so it is O(1); the
//     Python's `for i in range(5)` has a literal bound and the rest is
//     straight-line code, so the O(n) label is wrong for both.
//
//   how this label could be wrong, and what to check:
//     The label assumes growth in n, but the time string is always HH:MM.
//     Check `requires |time| == 5` and that Solve has no loop; ParseInt is
//     applied only to 1-character slices such as time[0..1], so its linear
//     cost is constant.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 26, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "ParseInt"],
//     "loop_depth": 0, "loops": 0, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 722_A. Broken Clock  (problem 2700, solution 2700_53)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(input())
// for i in range(5):
//     if (i != 2):
//         a[i] = int(a[i])
// n1 = a[0] * 10 + a[1]
// n2 = a[3] * 10 + a[4]
// if n == 24:
//     ans = 0
//     if (n1 >= 24):
//         a[0] = 0
//     if (n2 >= 60):
//         a[3] = 0
//     print(''.join(map(str, a)))
// if (n == 12):
//     if (n2 >= 60):
//         a[3] = 0
//     if (n1 == 0):
//         a[0] = 1
//     if (n1 > 12):
//         if (a[1] == 0):
//             a[0] = 1
//         else:
//             a[0] = 0
//     print(''.join(map(str, a)))
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, time: string) returns (output: string)
  requires |time| == 5
{
  var a0 := ParseInt(time[0..1]);
  var a1 := ParseInt(time[1..2]);
  var a3 := ParseInt(time[3..4]);
  var a4 := ParseInt(time[4..5]);
  var n1 := a0 * 10 + a1;
  var n2 := a3 * 10 + a4;
  output := "";
  if N == 24 {
    if n1 >= 24 { a0 := 0; }
    if n2 >= 60 { a3 := 0; }
    output := IntToString(a0) + IntToString(a1) + ":" + IntToString(a3) + IntToString(a4) + "\n";
  }
  if N == 12 {
    if n2 >= 60 { a3 := 0; }
    if n1 == 0 { a0 := 1; }
    if n1 > 12 {
      if a1 == 0 { a0 := 1; } else { a0 := 0; }
    }
    output := IntToString(a0) + IntToString(a1) + ":" + IntToString(a3) + IntToString(a4) + "\n";
  }
}
