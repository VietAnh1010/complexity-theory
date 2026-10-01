// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r4-d03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve builds d with one `while z < n + 4` loop and then runs a
//     single `while i < n` loop doing O(1) seq reads and updates, so it is
//     O(n). The Python builds [False] * (n + 4) and runs one for loop with
//     O(1) list updates, so it is linear too and the O(n**2) label is
//     wrong.
//
//   how this label could be wrong, and what to check:
//     The label claims quadratic work, but the body is one loop. Check
//     `while i < n` and the d setup loop `while z < n + 4`: both are
//     single passes, and `d := d[data[i] := false]` is an O(1) seq update
//     in this cost model.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 38, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 886_C. Petya and Catacombs  (problem 2505, solution 2505_30)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// data = list(map(int, input().split()))
// d = [False] * (n + 4)
// d[0] = True
// res = 1
// for i in range(n):
//     #print(d)
//     if d[data[i]]:
//         d[data[i]] = False
//         d[i + 1] = True
//     else:
//         d[i + 1] = True
//         res += 1
// #print(d)
// print(res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<seq<int>>) returns (output: string)
  requires n >= 0
  requires |coordinates| >= 1
  requires n <= |coordinates[0]|
  requires forall t :: 0 <= t < n ==> 0 <= coordinates[0][t] < n + 4
{
  var data := coordinates[0];
  var d: seq<bool> := [];
  var z := 0;
  while z < n + 4
    invariant 0 <= z <= n + 4
    invariant |d| == z
    decreases n + 4 - z
  {
    d := d + [false];
    z := z + 1;
  }
  d := d[0 := true];
  var res := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |d| == n + 4
    decreases n - i
  {
    if d[data[i]] {
      d := d[data[i] := false];
      d := d[i + 1 := true];
    } else {
      d := d[i + 1 := true];
      res := res + 1;
    }
    i := i + 1;
  }
  output := IntToString(res);
}
