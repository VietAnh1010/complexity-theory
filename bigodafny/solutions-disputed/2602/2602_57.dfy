// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops once over the pairs in pairs_list, calling SumSeq on a
//     two-element row (constant) and appending to lines, then a linear
//     Join, so it is O(n) in the number of tests; the Python's sum(list1)
//     over a two-number line is also constant per test, so the O(n*m)
//     label is wrong.
//
//   how this label could be wrong, and what to check:
//     The label assumes a second dimension m (row width), but each test
//     row is exactly two numbers a and b. Check the problem input format:
//     'a line of two integers a and b', so SumSeq(pairs_list[i]) is over 2
//     elements and the width never varies.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 15, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "SumSeq"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1351_A. A+B (Trial Problem)  (problem 2602, solution 2602_57)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// testcase = int(input())
// 
// for i in range(testcase):
//    list1 = list(map(int , input().split()))
//    sum1 = sum(list1)
//    print(sum1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, pairs_list: seq<seq<int>>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < |pairs_list|
    invariant 0 <= i <= |pairs_list|
    decreases |pairs_list| - i
  {
    lines := lines + [IntToString(SumSeq(pairs_list[i]))];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
