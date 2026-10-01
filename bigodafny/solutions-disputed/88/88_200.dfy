// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-fix
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Per test, ReverseString(string_list[2t]) and
//     ReverseString(string_list[2t+1]) each cost O(|s|) by the recursion
//     row, and the two scans over y and x are single bounded passes, so
//     the total is O(sum of string lengths), not quadratic. The Python's
//     x[::-1] and its two break loops are equally linear, so the label is
//     wrong, not the translation.
//
//   how this label could be wrong, and what to check:
//     The label claims quadratic cost, but the per-test work may be linear
//     in the two strings' lengths. Find ReverseString (it peels s[1..] and
//     appends [s[0]], O(|s|) by the recursion row) and the two search
//     loops that each stop at the first '1'; confirm no loop nests over
//     the same data and check the Python's x[::-1] and break loops are
//     linear too.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 48, "data_dependent_loops": 2, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 2, "loops": 3, "recursive_helpers": 1,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1202_A. You Are Given Two Binary Strings...  (problem 88, solution 88_200)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for u in range(int(input())):
//     x=input()[::-1]
//     y=input()[::-1]
//     a,b=0,0
//     for i in range(len(y)):
//         if(y[i]=='1'):
//             a=i+1
//             break
//     for i in range(len(x)):
//         if(x[i]=='1' and i+1>=a):
//             b=i+1
//             break
//     print(b-a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, string_list: seq<string>) returns (output: string)
  requires n >= 0
  requires |string_list| == 2 * n
{
  var parts: seq<string> := [];
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    decreases n - t
  {
    var x := ReverseString(string_list[2 * t]);
    var y := ReverseString(string_list[2 * t + 1]);
    var a := 0;
    var i := 0;
    var found := false;
    while i < |y| && !found
      decreases |y| - i
    {
      if y[i] == '1' {
        a := i + 1;
        found := true;
      }
      i := i + 1;
    }
    var b := 0;
    var j := 0;
    var found2 := false;
    while j < |x| && !found2
      decreases |x| - j
    {
      if x[j] == '1' && j + 1 >= a {
        b := j + 1;
        found2 := true;
      }
      j := j + 1;
    }
    parts := parts + [IntToString(b - a)];
    t := t + 1;
  }
  output := Join(parts, "\n");
}

function ReverseString(s: string): string
  decreases |s|
{
  if |s| == 0 then s else ReverseString(s[1..]) + [s[0]]
}
