// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn+mlogm)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     After SortInts on both sequences the loop decrements i from
//     bSorted[0]-1 one step per iteration, costing O(value of the smallest
//     wrong-solution time), which is not bounded by n or m; the Python has
//     the identical `while i >= 2*am ... i -= 1` loop, so the true cost is
//     O(nlogn + mlogm + max b_i).
//
//   how this label could be wrong, and what to check:
//     The label counts only the two sorts. Open the `while i >= 2 * am &&
//     amax <= i && i > 0` loop and check its start `i := bSorted[0] - 1`:
//     it decrements one at a time, so it runs about min(d_list) -
//     max(2*am, amax) times, a count set by input values. Statement caps
//     (<=100) do not make that constant; if you accept a cap as constant
//     the label stands.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 23, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 2, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": ["SortInts"], "uses_map":
//     false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 350_A. TL  (problem 305, solution 305_76)
// time complexity: O(nlogn+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m = map(int, input().split())
// a = list(map(int, input().split()))
// b = list(map(int, input().split()))
// a.sort()
// b.sort()
// am = a[0]
// bm = min(b)
// i = b[0] - 1
// while i >= 2*am and a[-1] <= i and i > 0:
//     i -= 1
// i+=1
// if i == 0 or not(i >= 2*am and a[-1] <= i and i > 0) or bm <= i:
//     print(-1)
// else:
//     print(i)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string)
  requires |c_list| >= 1 && |d_list| >= 1
{
  var aSorted := SortInts(c_list);
  var bSorted := SortInts(d_list);
  var am := aSorted[0];
  var bm := bSorted[0];
  var amax := aSorted[|aSorted| - 1];
  var i := bSorted[0] - 1;
  while i >= 2 * am && amax <= i && i > 0
    decreases i
  {
    i := i - 1;
  }
  i := i + 1;
  if i == 0 || !(i >= 2 * am && amax <= i && i > 0) || bm <= i {
    output := "-1";
  } else {
    output := IntToString(i);
  }
}
