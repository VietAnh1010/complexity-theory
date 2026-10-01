// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : main agent, override of labelaudit-r4-s03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Override of labelaudit-r4-s03's ok: two SortInts calls sit beside
//     the O(n*m) nested loop, so the tight class is O(n*m + n log n + m
//     log m) and the label is below it when one list is short; the Python
//     sorts both lists the same way. Decision A (2026-10-01) requires the
//     tight class.
//
//   how this label could be wrong, and what to check:
//     The label is the nested-loop term alone. Check the two SortInts
//     calls beside the nested loop: with m = 1 the sorts' n log n exceeds
//     n*m, so O(n*m) is below the tight class. The proof bound carries
//     both terms.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 35, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 2, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": ["SortInts"], "uses_map":
//     false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 489_B. BerSU Ball  (problem 1718, solution 1718_1166)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// boys = list(map(int, input().split()))
// m = int(input())
// girls = list(map(int, input().split()))
// boys.sort()
// girls.sort()
// mark = [0]*m
// for i in range(n):
//     for j in range(m):
//         #print("{} {}".format(i, j))
//         if mark[j] == 0 and abs(boys[i] - girls[j]) <= 1:
//             #print("{} {}".format(i, j))
//             mark[j] = 1
//             break
// print(mark.count(1))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N1: int, list1: seq<int>, N2: int, list2: seq<int>) returns (output: string)
  requires 0 <= N1 <= |list1|
  requires 0 <= N2 <= |list2|
{
  var boys := SortInts(list1);
  var girls := SortInts(list2);
  var mark := seq(N2, (idx: int) => 0);
  var cnt := 0;
  var bi := 0;
  while bi < N1
    invariant 0 <= bi
    invariant |mark| == N2
    invariant |boys| == |list1| && |girls| == |list2|
    decreases N1 - bi
  {
    var gj := 0;
    var matched := false;
    while gj < N2 && !matched
      invariant 0 <= gj
      invariant |mark| == N2
      decreases N2 - gj
    {
      if mark[gj] == 0 && AbsInt(boys[bi] - girls[gj]) <= 1 {
        mark := mark[gj := 1];
        matched := true;
        cnt := cnt + 1;
      }
      gj := gj + 1;
    }
    bi := bi + 1;
  }
  output := IntToString(cnt);
}
