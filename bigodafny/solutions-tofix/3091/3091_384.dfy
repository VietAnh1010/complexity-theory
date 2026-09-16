// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-23
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Each room record is a fixed two-element (pi, qi) pair per the
//     problem statement, so `a := a + pairs_list[i]` concatenates a
//     constant-size chunk n times with no read of `a` inside that loop,
//     and the second `while idx+1 < |a|` loop is a single O(n) scan;
//     Python's `a += list(map(int, ...))` plus its `while i<n*2` loop are
//     likewise O(n), not O(n*m) as labelled — sibling row 3091_1574 for
//     the same problem is correctly labelled O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes a growing row-width m, but the problem statement
//     fixes each room record to exactly two integers (pi, qi); check the
//     input format confirms a fixed 2-element row like the 396_361
//     rectangle precedent, which makes m a constant, not a real dimension.
//     Then confirm the first loop's `a := a + pairs_list[i]` never reads
//     `a[...]` inside that loop (so it is O(1) amortised per row) and the
//     second loop is a single O(n) scan over the flattened 2n-length
//     array.
//
//   structural facts (deterministic, from labelaudit.py):
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
