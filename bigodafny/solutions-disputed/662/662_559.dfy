// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-u01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve makes one loop over the n strings and does IsAllChar twice
//     plus Repeat("01", nn) per string, linear in each string's length m,
//     so O(n*m); the Python's strip calls and `ans + "01"` loop are linear
//     per string in CPython, so n**2 does not describe either program.
//
//   how this label could be wrong, and what to check:
//     The label O(n**2) squares one size, but the two sizes are the test
//     count and the string length. Find `IsAllChar(s, ...)` and
//     `Repeat("01", nn)` inside the single loop over binary_strings: one
//     linear pass per string, so no square of one size. The Python's `ans
//     = ans + "01"` loop looks quadratic in the string length; check
//     whether you count that concat as a copy (CPython in place makes it
//     linear).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 31, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join", "Repeat"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1342_B. Binary Period  (problem 662, solution 662_559)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def fun(s):
//   if s.strip("0") == "" or s.strip("1") == "":
//     return s
//  
//   ans = ""
//   n = len(s)
//  
//   for i in range(0, n):
//     if s[0] == "0":
//         ans = ans + "01"
//     else:
//         ans = ans + "10"
//     
//   
//   return ans
//  
// tc = int(input())
//  
// while tc > 0:
//    s = str(input())
//    print(fun(s))
//    tc = tc - 1
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
    var s := binary_strings[i];
    if IsAllChar(s, '0') || IsAllChar(s, '1') {
      parts := parts + [s + "\n"];
    } else {
      var nn := |s|;
      if s[0] == '0' {
        parts := parts + [Repeat("01", nn) + "\n"];
      } else {
        parts := parts + [Repeat("10", nn) + "\n"];
      }
    }
    i := i + 1;
  }
  output := Join(parts, "");
}

function IsAllChar(s: string, c: char): bool
  decreases |s|
{
  if |s| == 0 then true
  else s[0] == c && IsAllChar(s[1..], c)
}
