// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : low
//   auditor        : labelaudit-batch-05
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     IsAllChar and the Repeat("01", nn)/Repeat("10", nn) calls are each
//     O(|s|) per the cost table's explicit Repeat rule, so the Dafny is
//     linear in total string length rather than quadratic. Python's `ans =
//     ans + "01"` loop is the classic in-place string-concatenation
//     pattern, which CPython's refcount-1 optimization typically makes
//     amortized linear rather than the naively-assumed O(n**2), so the
//     label may be wrong on the Python side too rather than only on the
//     translation; I am not fully certain this optimization reliably
//     applies here.
//
//   structural facts (deterministic, from labelaudit.py):
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
