// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(1)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve calls DistributeMancala for each of 14 holes, and every inner
//     loop runs to the literal 14 or to x % 14 (at most 13), so the work
//     is a constant independent of the stone counts. The Python's
//     range(len(a)) loops and `range(1, x % 14 + 1)` are the same constant
//     bound, so the n**2 label matches neither.
//
//   how this label could be wrong, and what to check:
//     The label assumes quadratic growth, but the board is fixed at 14
//     holes. Check `requires |values| == 14`, the literal 14 loop bounds
//     in DistributeMancala, and that the sowing loop `while t <= r` is
//     bounded by r = x % 14, which is below the literal 14 and so
//     constant.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 55, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 4, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 975_B. Mancala  (problem 2639, solution 2639_73)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = list(map(int, input().split()))
// 
// ans = 0
// for i in range(len(a)):
//     x = a[i]
//     b = [j for j in a]
//     b[i] = 0
//     for j in range(len(a)):
//         b[j] += x // 14
//     
//     for j in range(1, x % 14 + 1):
//         b[(i + j) % 14] += 1
//         
//     ans_now = 0
//     for j in b:
//         if j % 2 == 0:
//             ans_now += j
//     ans = max(ans_now, ans)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method DistributeMancala(a: seq<int>, i: int) returns (result: int)
  requires |a| == 14
  requires 0 <= i < 14
{
  var x := a[i];
  var b := a[i := 0];
  var q := if x >= 0 then x / 14 else 0;
  var j := 0;
  while j < 14
    invariant 0 <= j <= 14
    invariant |b| == 14
    decreases 14 - j
  {
    b := b[j := b[j] + q];
    j := j + 1;
  }
  var r := if x >= 0 then x % 14 else 0;
  var t := 1;
  while t <= r
    invariant |b| == 14
    decreases r - t
  {
    var idx := (i + t) % 14;
    b := b[idx := b[idx] + 1];
    t := t + 1;
  }
  var s := 0;
  var k := 0;
  while k < 14
    invariant 0 <= k <= 14
    invariant |b| == 14
    decreases 14 - k
  {
    if b[k] % 2 == 0 { s := s + b[k]; }
    k := k + 1;
  }
  result := s;
}

method Solve(values: seq<int>) returns (output: string)
  requires |values| == 14
{
  var ans := 0;
  var i := 0;
  while i < 14
    invariant 0 <= i <= 14
    decreases 14 - i
  {
    var ansNow := DistributeMancala(values, i);
    if ansNow > ans { ans := ansNow; }
    i := i + 1;
  }
  output := IntToString(ans);
}
