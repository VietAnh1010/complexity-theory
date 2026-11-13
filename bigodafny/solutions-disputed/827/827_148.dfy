// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : low
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     For each doctor the Dafny loops `while i <= last` adding j, about
//     last/j iterations, and `last` can grow by up to max d per doctor,
//     giving O(n * max s + n**2 * max d); the Python's `while
//     i<=dates[-1]: i += j` is the same loop.
//
//   how this label could be wrong, and what to check:
//     The inner `while i <= last` adds d each step, so it runs about
//     last/d times, and last grows by up to max d per doctor. Alternating
//     doctors with d = 1000 and d = 1 makes the total about n**2 * max d.
//     Check whether the problem's d cap is treated as a size (then
//     value-bounded) or a constant; leaning value term.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 25, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 879_A. Borya's Diagnosis  (problem 827, solution 827_148)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// arr = [[0,0] for i in range(n)]
// 
// for i in range(n):
//     arr[i][0] , arr[i][1] = map(int , input().split())
// 
// # arr.sort(key = lambda x: x[1])
// dates = [arr[0][0]]
// 
// for i,j in arr[1:]:
//     while i<=dates[-1] : i += j
//     dates.append(i)
// 
// 
// print(dates[-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<(int, int)>) returns (output: string)
  requires |pairs| >= 1
  requires forall k :: 0 <= k < |pairs| ==> 1 <= pairs[k].0 <= 1000 && 1 <= pairs[k].1 <= 1000
{
  var last := pairs[0].0;
  var idx := 1;
  while idx < |pairs|
    invariant 1 <= idx <= |pairs|
    decreases |pairs| - idx
  {
    var i := pairs[idx].0;
    var j := pairs[idx].1;
    while i <= last
      invariant j >= 1
      decreases last - i
    {
      i := i + j;
    }
    last := i;
    idx := idx + 1;
  }
  output := IntToString(last) + "\n";
}
