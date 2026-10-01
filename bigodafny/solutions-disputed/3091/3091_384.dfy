// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-08
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The first loop concatenates each two-element row onto a (cost
//     O(|row|) = 2 per row) and the second loop steps through a by twos,
//     so Solve is O(n). The Python's `a+=list(map(int,input().split()))`
//     adds two ints per line and its while loop runs n times, so it is
//     O(n) and the O(n*m) label is wrong.
//
//   how this label could be wrong, and what to check:
//     The label assumes variable row width m. Check the statement: each of
//     the n lines holds exactly two integers pi and qi, so the width is a
//     constant; if rows could be longer the label would stand.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 26, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 467_A. George and Accommodation  (problem 3091, solution 3091_384)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=[]
// count=0
// for x in range(n):
//     a+=list(map(int,input().split()))
// i=0
// while i<n*2:
//     if abs(a[i]-a[i+1])>=2:
//         count+=1
//     i+=2
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs_list: seq<seq<int>>) returns (output: string)
{
  var a: seq<int> := [];
  var i := 0;
  while i < |pairs_list|
    invariant 0 <= i <= |pairs_list|
    decreases |pairs_list| - i
  {
    a := a + pairs_list[i];
    i := i + 1;
  }
  var count := 0;
  var idx := 0;
  while idx + 1 < |a|
    invariant 0 <= idx
    decreases |a| - idx
  {
    if AbsInt(a[idx] - a[idx + 1]) >= 2 {
      count := count + 1;
    }
    idx := idx + 2;
  }
  output := IntToString(count);
}
