// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     After `SortInts(a_list)` the Dafny calls `ISqrt(v)` for each
//     nonnegative element, charged O(log v), so the cost is O(n log n + n
//     log max a_i); the Python's `ps` takes the same square roots.
//
//   how this label could be wrong, and what to check:
//     The label counts the sort but charges each square root 1. Check the
//     loop: each nonnegative element calls `ISqrt(v)`, charged O(log v), a
//     value term; the Python's `ps(i)` takes `sqrt(n)` for the same
//     elements.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 23, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": ["SortInts"], "uses_map":
//     false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 914_A. Perfect Squares  (problem 2358, solution 2358_103)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import sqrt as S
// def ps(n):
//     return int(S(n))!=S(n)
// n=int(input())
// l=sorted([int(i) for i in input().split()])
// for i in l:
//     if i<0:
//         ans=i 
//     elif ps(i):
//         ans=i
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var l := SortInts(a_list);
  var ans := 0;
  var i := 0;
  while i < |l|
    decreases |l| - i
  {
    var v := l[i];
    if v < 0 {
      ans := v;
    } else {
      var r := ISqrt(v);
      if r * r != v {
        ans := v;
      }
    }
    i := i + 1;
  }
  output := IntToString(ans);
}
