// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-09
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny never calls SortInts; it checks the string is
//     non-decreasing with one forward pass comparing s[i] to s[i+1], so
//     the whole method is O(n), while Python's `sorted(s)` call makes the
//     original O(n log n).
//
//   how this label could be wrong, and what to check:
//     The label assumes the Dafny needs Python's sort to check ordering.
//     Open the first while loop (`while i + 1 < n`) and confirm it only
//     compares adjacent characters s[i] and s[i+1] with no call to
//     SortInts or Sort anywhere in the file; if so the method is a single
//     linear pass, not O(n log n).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 30, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 2,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 960_A. Check the string  (problem 1368, solution 1368_67)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import defaultdict
// s = list(input())
// t = sorted(s)
// flag = True
// if s[0] != "a":
//     flag = False
// if s != t:
//     flag = False
// dic = defaultdict(int)
// for i in s:
//     dic[i] += 1
//
// if dic["a"] == 0 or dic["b"] == 0:
//     flag = False
//
// if dic["a"] != dic["c"] and dic["b"] != dic["c"]:
//     flag = False
//
// if flag:
//     print("YES")
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  var n := |s|;
  var flag := true;
  if n == 0 || s[0] != 'a' { flag := false; }
  var i := 0;
  while i + 1 < n
    decreases n - i
  {
    if s[i] > s[i+1] { flag := false; }
    i := i + 1;
  }
  var ca := 0;
  var cb := 0;
  var cc := 0;
  i := 0;
  while i < n
    decreases n - i
  {
    if s[i] == 'a' { ca := ca + 1; }
    else if s[i] == 'b' { cb := cb + 1; }
    else if s[i] == 'c' { cc := cc + 1; }
    i := i + 1;
  }
  if ca == 0 || cb == 0 { flag := false; }
  if ca != cc && cb != cc { flag := false; }
  output := if flag then "YES" else "NO";
}
