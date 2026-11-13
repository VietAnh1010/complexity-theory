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
//     The Dafny calls `SumSeq(s)` and `MinSeq(s)` on each of n rows, as
//     the Python calls `sum` and `min`, but every row is a fixed
//     three-number test case, so the cost is O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes the row width varies. `sum(s)` and `min(s)` walk
//     each row, but each test case is exactly three monster healths a, b,
//     c. Check the input format; three numbers per line make m a constant
//     and the class O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 23, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join", "MinSeq", "SumSeq"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1463_A. Dungeon  (problem 2870, solution 2870_46)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// for i in range(n):
//     s = list(map(int, input().split()))
//     d = sum(s)
//     if min(s) >= d // 9 and d % 9 == 0:
//         print('YES')
//     else:
//         print('NO')
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values_list: seq<seq<int>>) returns (output: string)
  requires |values_list| == n
  requires forall k :: 0 <= k < |values_list| ==> |values_list[k]| > 0
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
  {
    var s := values_list[i];
    var d := SumSeq(s);
    var m := MinSeq(s);
    if m >= d / 9 && d % 9 == 0 {
      lines := lines + ["YES"];
    } else {
      lines := lines + ["NO"];
    }
    i := i + 1;
  }
  output := if |lines| > 0 then Join(lines, "\n") + "\n" else "";
}
