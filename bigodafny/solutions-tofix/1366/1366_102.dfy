// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-08
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny replaces Python's two `sorted(...)` calls with two O(n)
//     linear scans over a_list that track the extremal odd value directly
//     (confirmed by the empty `sorts` fact), so the Dafny's tight class is
//     O(n) even though Python's use of sorted() genuinely makes it O(n log
//     n) as labelled.
//
//   how this label could be wrong, and what to check:
//     The label assumes the Dafny sorts as Python does with
//     `sorted(n)[::-1]` and `sorted(p)`. Check the `sorts` fact (it is
//     empty) and confirm the Dafny instead does two linear scans over
//     a_list tracking the best odd negative and odd positive directly,
//     which is O(n), not O(n log n); this makes the Dafny faster than its
//     label, an inverse of the usual translation defect.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 37, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 3, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 797_B. Odd sum  (problem 1366, solution 1366_102)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// '''input
// 10
// 1184 5136 1654 3254 6576 6900 6468 327 179 7114
// '''
// input()
// a = list(map(int, input().split()))
// s = 0
// p, n = [i for i in a if i > 0], [j for j in a if j < 0]
// s = sum(p)
// if s % 2 == 1:
// 	print(s)
// else:
// 	m = -10000000
// 	for x in sorted(n)[::-1]:
// 		if x % 2 == 1:
// 			m = x
// 			break
// 	for y in sorted(p):
// 		if y % 2 == 1:
// 			m = max(m, -y)
// 	print(s + m)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var s := 0;
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    if a_list[i] > 0 { s := s + a_list[i]; }
    i := i + 1;
  }
  if FloorMod(s, 2) == 1 {
    output := IntToString(s);
  } else {
    // sorted(n)[::-1] scanned for first odd == max odd negative (order-independent).
    var m := -10000000;
    var j := 0;
    while j < |a_list|
      decreases |a_list| - j
    {
      if a_list[j] < 0 && FloorMod(a_list[j], 2) == 1 && a_list[j] > m {
        m := a_list[j];
      }
      j := j + 1;
    }
    j := 0;
    while j < |a_list|
      decreases |a_list| - j
    {
      if a_list[j] > 0 && FloorMod(a_list[j], 2) == 1 && -a_list[j] > m {
        m := -a_list[j];
      }
      j := j + 1;
    }
    output := IntToString(s + m);
  }
}
