// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-23
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The nested loops `while r < |v_3|` (n floors) and inner `while i <
//     2*m` (m flats per floor) together scan all n*m entries, and the
//     Python does the same with `for _ in range(n)` plus `sum(... for i in
//     range(0, m*2, 2))`, so both sources are O(n*m), not O(n) as
//     labelled; sibling row 3046_65 for the same problem is correctly
//     labelled O(n*m).
//
//   how this label could be wrong, and what to check:
//     The label assumes only the floor count n matters, but the problem
//     statement gives `1 <= n, m <= 100` as two independent parameters and
//     each floor line has 2m characters that the inner loop `while i <
//     2*m` fully scans for every one of n floors. Confirm m is not fixed
//     (unlike the 396_361 rectangle case) by rereading the input format,
//     then check the inner loop bound `i < 2*m` runs to completion each
//     outer iteration, giving O(n*m); compare directly against sibling
//     `3046_65`, labelled O(n*m) for the identical problem.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 26, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 595_A. Vitaly and Night  (problem 3046, solution 3046_103)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, m = map(int, input().split())
// 
// ans = 0
// for _ in range(n):
// 	windows = list(map(int, input().split()))
// 	ans += sum(min(1, windows[i] + windows[i + 1]) for i in range(0, m * 2, 2))
// 
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, v_3: seq<seq<int>>) returns (output: string)
{
  var ans := 0;
  var r := 0;
  while r < |v_3|
    invariant 0 <= r <= |v_3|
    decreases |v_3| - r
  {
    var windows := v_3[r];
    var i := 0;
    while i < 2 * m
      invariant 0 <= i
      decreases 2 * m - i
    {
      if i + 1 < |windows| {
        var s := windows[i] + windows[i + 1];
        ans := ans + (if s < 1 then s else 1);
      }
      i := i + 2;
    }
    r := r + 1;
  }
  output := IntToString(ans);
}
