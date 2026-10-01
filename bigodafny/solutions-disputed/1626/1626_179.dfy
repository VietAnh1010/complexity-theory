// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-09
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Sort costs O(n log n), but the outer while low<high halves a range
//     of size about sum(a) (values up to 10^9), each iteration running the
//     inner i-loop up to n steps, so the total is O(n log n + n log(sum
//     a_i)), a value term the label omits.
//
//   how this label could be wrong, and what to check:
//     The label counts only the sort, but the outer while low<high
//     binary-searches over a value range up to SumSeq(a), so the cost has
//     an extra log(sum a_i) factor times n. Check the outer loop's
//     decreases high-low and the inner loop scanning a[i] up to n times
//     per mid; the Python has the same structure so the label would be
//     wrong for both.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 36, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "SumSeq"],
//     "loop_depth": 2, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     ["Sort"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 348_A. Mafia  (problem 1626, solution 1626_179)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// n = int(input())
// a = [int(x) for x in input().split()]
// a.sort(reverse=True)
// low = a[0]
// high = sum(a)
// while low < high:
// 	mid = (low + high) // 2
// 	t = 0
// 	i = 0
// 	while i < n and t < mid:
// 		if t >= a[i]:
// 			t = mid
// 			break
// 		t += (mid - a[i])
// 		i += 1
// 	if t >= mid:
// 		high = mid
// 	else:
// 		low = mid + 1
// print(high)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| == n
  requires n >= 1
{
  var a := Sort(a_list, (x: int, y: int) => x > y);
  var low := a[0];
  var high := SumSeq(a);
  while low < high
    decreases high - low
  {
    var mid := (low + high) / 2;
    var t := 0;
    var i := 0;
    var brk := false;
    while i < n && t < mid && !brk
      invariant 0 <= i <= n
      decreases !brk, n - i
    {
      if t >= a[i] {
        t := mid;
        brk := true;
      } else {
        t := t + (mid - a[i]);
        i := i + 1;
      }
    }
    if t >= mid {
      high := mid;
    } else {
      low := mid + 1;
    }
  }
  output := IntToString(high);
}
