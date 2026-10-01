// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Both branches loop `while i + 1 < |s|` stepping by 2 and building
//     parts, then Join(parts, "-") is linear in output length, so cost is
//     O(n) in |s|; the Python's zip(s[::2], s[1::2]) and '-'.join are also
//     linear.
//
//   how this label could be wrong, and what to check:
//     The label O(1) assumes straight-line code, but the Dafny loops
//     `while i + 1 < |s|` over the whole phone string and then calls Join
//     over the parts. Check the problem statement: n is the digit count
//     (2..100), but a cap is not a literal in the source, and the Python's
//     zip/join over s is likewise linear.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 31, "data_dependent_loops": 2, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 1, "loops":
//     2, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 25_B. Phone numbers  (problem 1966, solution 1966_144)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = input()
// if n > 3:
//     if n % 2 == 0:
//         res = '-'.join(a + b for a, b in zip(s[::2], s[1::2]))
//     else:
//         res = s[0:3] + '-' + '-'.join(a + b for a, b in zip(s[3::2], s[4::2]))
//     print(res)
// else:
//     print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
  requires |s| == n
{
  if n > 3 {
    var res: string;
    if n % 2 == 0 {
      var parts: seq<string> := [];
      var i := 0;
      while i + 1 < |s|
      {
        parts := parts + [s[i..i+2]];
        i := i + 2;
      }
      res := Join(parts, "-");
    } else {
      var parts: seq<string> := [];
      var i := 3;
      while i + 1 < |s|
      {
        parts := parts + [s[i..i+2]];
        i := i + 2;
      }
      res := s[0..3] + "-" + Join(parts, "-");
    }
    output := res + "\n";
  } else {
    output := s + "\n";
  }
}
