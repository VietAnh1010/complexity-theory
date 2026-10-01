// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r3d-02
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python takes (a*b)**0.5 in O(1) per query, so it is O(Q), but
//     the Dafny's IntSqrt method binary-searches lo/hi, costing
//     O(log(a*b)) per query, i.e. O(n log max(a_i b_i)) overall. The Dafny
//     pays a value term via a reimplemented sqrt that the Python does not,
//     which is the sqrt-search translation shape.
//
//   how this label could be wrong, and what to check:
//     The label is right about the Python, which computes
//     `floor((a*b)**0.5)` once per query. Check that IntSqrt does a binary
//     search over [0, x+1] with about log2(a*b) iterations per query.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 49, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
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
      var t := IntSqrt(a * b);
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

method IntSqrt(x: int) returns (r: int)
  requires x >= 0
{
  if x == 0 {
    return 0;
  }
  var lo := 0;
  var hi := x + 1;
  while lo + 1 < hi
    invariant 0 <= lo < hi
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if mid * mid <= x {
      lo := mid;
    } else {
      hi := mid;
    }
  }
  r := lo;
}
