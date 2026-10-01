// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : low
//   auditor        : labelaudit-r3-04
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Solve loop runs over binary_strings (n items), but each
//     iteration calls the recursive CountChar twice and Repeat on t,
//     costing O(|t|), and Join costs the total output length; the Python's
//     t.count and '01'*len(t) pay the same per-string width.
//
//   how this label could be wrong, and what to check:
//     The label assumes cost is linear in the count n of test strings. The
//     Dafny's CountChar and Repeat("01", |t|) walk each string, so cost is
//     the sum of the string lengths. Check whether the dataset's n means
//     total input size or the number of strings; if it is the count of
//     strings, the label omits the width and O(n*m) is right, and if it is
//     total characters the label stands.
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
