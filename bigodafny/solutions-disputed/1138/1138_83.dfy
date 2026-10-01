// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve has a single loop `while i < n` reading data[i][0] and
//     data[i][1], with FloorMod(.., m) as O(1) arithmetic; m is the skip
//     value x, not a size, and the Python is the same single loop, so the
//     cost is O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes m is a size dimension. Check how m is used in the
//     Dafny: it appears only as the divisor in FloorMod(..., m), which is
//     the problem's value x, never as a loop bound.
//
//   structural facts (deterministic, from label_audit.py):
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
