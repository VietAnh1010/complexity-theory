// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r4-u01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over T binary strings and for each calls CountChar twice
//     and Repeat("01", |t|), all linear in that string's length, so n
//     strings each scanned once is O(n*m); the Python's t.count and '01' *
//     len(t) per test do the same, so the O(n) label names only one of the
//     two sizes.
//
//   how this label could be wrong, and what to check:
//     The label O(n) counts only the T test strings, but each one is
//     scanned in full. Find CountChar(t, '1') and CountChar(t, '0')
//     (recursion over every character of t) and Repeat("01", |t|); confirm
//     each test line is a string of up to 100 characters, so the width m
//     is a separate size from T.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 28, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join", "Repeat"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1342_B. Binary Period  (problem 662, solution 662_527)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # list( map(int, input().split()) )
// rw = int(input())
// for ewqr in range(rw):
//     t = input()
//     if t.count('1') == 0 or t.count('0') == 0:
//         print(t)
//         continue
//     s = '01' * len(t)
//     print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, binary_strings: seq<string>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n && i < |binary_strings|
    invariant 0 <= i
    decreases n - i
  {
    var t := binary_strings[i];
    var c1 := CountChar(t, '1');
    var c0 := CountChar(t, '0');
    if c1 == 0 || c0 == 0 {
      parts := parts + [t + "\n"];
    } else {
      parts := parts + [Repeat("01", |t|) + "\n"];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}

function CountChar(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}
