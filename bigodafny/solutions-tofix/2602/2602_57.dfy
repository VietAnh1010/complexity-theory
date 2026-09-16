// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-19
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     SumSeq(pairs_list[i]) sums each row, but the description fixes every
//     test case to exactly two integers a and b, so SumSeq costs O(1) not
//     O(m); the loop over N rows is then O(n) not O(n*m), matching the
//     Python's O(1)-per-line sum(list1) loop.
//
//   how this label could be wrong, and what to check:
//     The label assumes row width m varies with input. Check the
//     description: each test case is given as 'a line of two integers a
//     and b', a fixed 2-tuple, not a ragged row. If confirmed,
//     SumSeq(pairs_list[i]) costs O(1) per row, not O(m), and the loop
//     over N rows collapses to O(n).
//
//   structural facts (deterministic, from labelaudit.py):
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
