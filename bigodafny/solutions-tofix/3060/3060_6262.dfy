// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n+m)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-23
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Python's `sort(n[i], m[i])` sorts a fixed 2-character string (`x+y`
//     from two single-char indices) at O(1), not an n-sized collection, so
//     the surrounding `for i in range(0, len(n))` loop is O(n) overall;
//     the Dafny mirrors this with a direct `if n[i] > m[i]` comparison in
//     a single scan, matching the O(n+m) convention used by sibling row
//     3060_1359 for the same problem, not O(nlogn).
//
//   how this label could be wrong, and what to check:
//     The label assumes a real sort over an n-sized collection, but the
//     Python's `sort(n[i], m[i])` helper calls `sorted(x+y)` where x and y
//     are single characters, so it always sorts a length-2 string
//     regardless of input size. Open the Python `sort` helper and confirm
//     its argument is always 2 characters; then note the Dafny's
//     equivalent is a plain `if n[i] > m[i]` comparison inside a single
//     O(n+m) scan, with no log factor anywhere.
//
//   structural facts (deterministic, from labelaudit.py):
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
