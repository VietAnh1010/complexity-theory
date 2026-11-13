// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     For each of the q queries the Dafny calls `ISqrt(a * b)`, charged
//     its O(log(a*b)) depth, so the cost is O(q log max(a_i * b_i)); the
//     Python's `floor((a*b)**0.5)` is the same square root.
//
//   how this label could be wrong, and what to check:
//     The label charges each query 1, but each query takes `ISqrt(a * b)`,
//     charged O(log(a*b)), a value term; the Python takes `(a*b)**0.5` at
//     the same point. Check that the per-query work is otherwise constant;
//     then the class is O(q log max(a*b)).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 28, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// p03388 AtCoder Beginner Contest 093 - Worst Case  (problem 810, solution 810_131)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// q=int(input())
// ab=[list(map(int,input().split())) for _ in range(q)]
// from math import floor
// for a,b in ab:
//   if a==b:
//     print(2*a-2)
//     continue
//   t=floor((a*b)**0.5)
//   # t,t+1 組み合わせの積がa*bで抑えられているかどうか
//   if t*t>=a*b: # t*tもだめ
//     print(2*t-3)
//   elif t*(t+1)>=a*b: # t*(t+1)はだめ
//     print(2*t-2)
//   else: # t*tもt*(t+1)もOK
//     print(2*t-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2 && pairs[k][0] >= 0 && pairs[k][1] >= 0
{
  output := "";
  var idx := 0;
  while idx < |pairs|
    invariant 0 <= idx <= |pairs|
    decreases |pairs| - idx
  {
    var a := pairs[idx][0];
    var b := pairs[idx][1];
    if a == b {
      output := output + IntToString(2 * a - 2) + "\n";
    } else {
      var t := ISqrt(a * b);
      if t * t >= a * b {
        output := output + IntToString(2 * t - 3) + "\n";
      } else if t * (t + 1) >= a * b {
        output := output + IntToString(2 * t - 2) + "\n";
      } else {
        output := output + IntToString(2 * t - 1) + "\n";
      }
    }
    idx := idx + 1;
  }
}
