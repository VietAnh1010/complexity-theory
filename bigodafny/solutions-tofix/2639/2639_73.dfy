// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(1)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-20
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The outer loop in Solve and all three loops in DistributeMancala
//     (over j, over t up to r = x % 14 <= 13, and over k) are bounded by
//     the literal constant 14, matching the fixed 14-hole board in the
//     description, so the whole computation is O(1); the Python mirrors
//     this with range(len(a)) and range(1, x % 14 + 1) over the same
//     fixed-size list.
//
//   how this label could be wrong, and what to check:
//     The label assumes a scaling n, but Solve(values: seq<int>) requires
//     |values| == 14 and the description fixes the board at 14 integers.
//     Check that every loop in DistributeMancala and Solve is bounded by
//     the literal 14 (or by r <= 13, itself bounded by x % 14), never by
//     |values| or a derived n, which would mean the method is
//     constant-time.
//
//   structural facts (deterministic, from labelaudit.py):
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
