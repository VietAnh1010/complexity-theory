// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-08
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny lowercases both strings with seq comprehensions and runs
//     one `while i < |n|` loop with an O(1) comparison, so it is O(n). The
//     Python's sorted(x+y) is applied to two characters at a time, a
//     constant-size sort, so the Python is O(n) too and the O(nlogn) label
//     is wrong.
//
//   how this label could be wrong, and what to check:
//     The label assumes a real sort. Check the Python's helper `sort(x,
//     y)`: it sorts x+y, which is two single characters, so the sort is
//     O(1) per call; the Dafny likewise takes a two-way max inside one
//     loop.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 34, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 112_A. Petya and Strings  (problem 3060, solution 3060_6262)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def sort(x, y):
//     a=sorted(x+y)
//     return a[-1]
// 
// n=input().lower()
// m=input().lower()
// 
// for i in range (0, len(n)):
//     if n[i]==m[i]:
//         if i==len(n)-1:
//             print(0)
//         continue
//     else:
//         if sort(n[i], m[i])==n[i]:
//             print(1)
//             break
//         else:
//             print(-1)
//             break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s1: string, s2: string) returns (output: string)
{
  var n: seq<char> := seq(|s1|, k requires 0 <= k < |s1| =>
    if s1[k] >= 'A' && s1[k] <= 'Z' then ((s1[k] as int) + 32) as char else s1[k]);
  var m: seq<char> := seq(|s2|, k requires 0 <= k < |s2| =>
    if s2[k] >= 'A' && s2[k] <= 'Z' then ((s2[k] as int) + 32) as char else s2[k]);
  var i := 0;
  while i < |n|
    invariant 0 <= i <= |n|
    decreases |n| - i
  {
    if i < |m| && n[i] == m[i] {
      if i == |n| - 1 {
        output := "0";
        return;
      }
      i := i + 1;
    } else if i < |m| {
      var mx := if n[i] > m[i] then n[i] else m[i];
      if mx == n[i] {
        output := "1";
      } else {
        output := "-1";
      }
      return;
    } else {
      output := "0";
      return;
    }
  }
  output := "0";
}
