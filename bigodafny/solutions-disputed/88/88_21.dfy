// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Per test the Dafny calls ReverseString(b) and ReverseString(a) (each
//     O(|s|)) and scans bRev and aRev, so cost is O(sum of |x_i|+|y_i|),
//     not O(n tests); the Python's [::-1], index and slice are linear in
//     length as well.
//
//   how this label could be wrong, and what to check:
//     The label's n counts test cases, but each test scans two strings
//     whose lengths the label does not name. Check the loops over bRev and
//     aRev and ReverseString in Solve, and the statement's bound of total
//     length of x and y at most 10^5 each; if the label is meant as total
//     input size it would stand.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 50, "data_dependent_loops": 2, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 2, "loops": 3, "recursive_helpers": 1,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1202_A. You Are Given Two Binary Strings...  (problem 88, solution 88_21)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// for i in range(n):
// 	a=input()
// 	b=input()
// 	k=b[::-1].index("1")
// 	a=a[::-1]
// 	p=a[k::].index("1")
// 	print(p)
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
    var a := string_list[2 * t];
    var b := string_list[2 * t + 1];
    var bRev := ReverseString(b);
    var k := 0;
    var found := false;
    var i := 0;
    while i < |bRev| && !found
      decreases |bRev| - i
    {
      if bRev[i] == '1' {
        k := i;
        found := true;
      }
      i := i + 1;
    }
    var aRev := ReverseString(a);
    var p := 0;
    var found2 := false;
    var j := k;
    while j < |aRev| && !found2
      decreases |aRev| - j
    {
      if aRev[j] == '1' {
        p := j - k;
        found2 := true;
      }
      j := j + 1;
    }
    parts := parts + [IntToString(p)];
    t := t + 1;
  }
  output := Join(parts, "\n");
}

function ReverseString(s: string): string
  decreases |s|
{
  if |s| == 0 then s else ReverseString(s[1..]) + [s[0]]
}
