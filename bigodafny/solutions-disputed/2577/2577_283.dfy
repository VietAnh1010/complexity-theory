// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny calls `SumSeq(mat[i])` on each of n rows, and the Python
//     `sum(l)`, but each row is a fixed three-number test case, so the
//     cost is O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes the row width varies. `sum(l)` walks each row, but
//     each test case is exactly three side lengths a, b, c. Check the
//     input format; three numbers per line make m a constant and the class
//     O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 16, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "SumSeq"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1422_A. Fence  (problem 2577, solution 2577_283)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// import math
// 
// input = sys.stdin.readline
// 
// def inInt():
//     return int(input())
// 
// def inStr():
//     return input().strip("\n")
// 
// def inIList():
//     return (list(map(int, input().split())))
// 
// def inSList():
//     return (input().split())
// 
// #########################################
// 
// def solve(l):
//     print(sum(l) - 1)
// 
// tasks = inInt()
// for t in range(tasks):
//     l = inIList()
//     solve(l)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, mat: seq<seq<int>>) returns (output: string)
  requires n <= |mat|
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var s := SumSeq(mat[i]) - 1;
    lines := lines + [IntToString(s)];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
