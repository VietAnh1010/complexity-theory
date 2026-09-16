// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r2-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The single while loop iterates over n rows of `data`, reading only
//     data[i][0] and data[i][1] (and data[i-1][1]) with O(1) FloorMod and
//     arithmetic per iteration; the parameter m is the skip value x used
//     only as a modulus operand, never as a loop bound or a scanned
//     dimension, so the true class is O(n), matching sibling 1138_66's
//     identical O(n) label for the same problem.
//
//   how this label could be wrong, and what to check:
//     The label O(n*m) implies the loop's cost scales with m, but m here
//     is the skip-length x (a `requires m > 0` scalar), used only inside
//     `FloorMod(..., m)` as an O(1) arithmetic operand, never as a range
//     or size that gets walked. Confirm no loop in the Dafny iterates 'm
//     times' or over a structure of length m; if none exists, compare to
//     sibling 1138_66 (same problem, same structure, labeled O(n)) to
//     confirm O(n) is correct here too.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 24, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 499_A. Watching a movie  (problem 1138, solution 1138_83)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,x = map(int, input().split())
// data = []
// result = 0
// 
// for _ in range(n):
//     data.append(list(map(int, input().split())))
// 
// for i in range(n):
//     if i==0:
//         result += (data[i][0]-1)%x
//     else:
//         result += (data[i][0]-data[i-1][1]-1)%x
//     result += data[i][1]-data[i][0]+1
// 
// print(result)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, data: seq<seq<int>>) returns (output: string)
  requires n >= 0
  requires m > 0
  requires n == |data|
  requires forall k :: 0 <= k < n ==> |data[k]| >= 2
{
  var result := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    if i == 0 {
      result := result + FloorMod(data[i][0] - 1, m);
    } else {
      result := result + FloorMod(data[i][0] - data[i-1][1] - 1, m);
    }
    result := result + data[i][1] - data[i][0] + 1;
    i := i + 1;
  }
  output := IntToString(result);
}
