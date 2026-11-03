// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3-02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Each of the n elements runs the inner loop `while j * j <= v` for
//     about sqrt(v) iterations, a cost in the element value; the Python
//     does the same with range(1, int(i**.5)+1) over set(a), so the true
//     cost is O(n sqrt(max a_i)) and the label omits that value term.
//
//   how this label could be wrong, and what to check:
//     The label counts only the n elements, but each element runs an inner
//     divisor search up to its square root. Open the `while j * j <= v`
//     loop inside the per-element loop and compare with the Python's `for
//     j in range(1, int(i**.5)+1)`; if the Python took sqrt in O(1)
//     without a loop the cause would differ, but it loops too.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 41, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 4, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1113_B. Sasha and Magnetic Machines  (problem 342, solution 342_86)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// input()
// a = list(map(int , input().split()))
// m = min(a)
// print(sum(a)-max(i+m-i//j-m*j for i in set(a)
// for j in range(1 , int(i**.5) + 1)if i%j==0))
// --------------------------------------------------------------------

include "../../../prelude.dfy"

ghost function SqPref342(a: seq<int>, i: nat): nat
  requires i <= |a|
  decreases i
{
  if i == 0 then 0 else SqPref342(a, i - 1) + ISqrt(if a[i - 1] > 0 then a[i - 1] else 0)
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires |a_list| >= 1
  ensures steps <= 20 * |a_list| + 12 * SqPref342(a_list, |a_list|) + 8 + |output|
{
  steps := 0;
  var total := 0;
  var idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant steps == 6 * idx
    decreases |a_list| - idx
  {
    steps := steps + 3;
    steps := steps + 2;
    total := total + a_list[idx];
    steps := steps + 1;
    idx := idx + 1;
  }
  steps := steps + 2;
  steps := steps + 1;
  var m := a_list[0];
  idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant steps <= 6 * |a_list| + 3 + 7 * idx
    decreases |a_list| - idx
  {
    steps := steps + 3;
    steps := steps + 2;
    if a_list[idx] < m {
      steps := steps + 1;
      m := a_list[idx];
    }
    steps := steps + 1;
    idx := idx + 1;
  }
  steps := steps + 2;
  var diff := 0;
  idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant steps <= 13 * |a_list| + 5 + 7 * idx + 12 * SqPref342(a_list, idx)
    decreases |a_list| - idx
  {
    steps := steps + 3;
    steps := steps + 1;
    var v := a_list[idx];
    var j := 1;
    ghost var vv: nat := if v > 0 then v else 0;
    ghost var s1 := steps;
    while j * j <= v
      invariant 1 <= j
      invariant (j - 1) * (j - 1) <= vv
      invariant steps <= s1 + 12 * (j - 1)
      decreases v - j * j
    {
      steps := steps + 3;
      steps := steps + 2;
      if v % j == 0 {
        steps := steps + 5;
        var term := v + m - v / j - m * j;
        steps := steps + 1;
        if term > diff {
          diff := term;
        }
      }
      steps := steps + 1;
      j := j + 1;
    }
    LeISqrt(j - 1, vv);
    steps := steps + 2;
    steps := steps + 1;
    idx := idx + 1;
  }
  steps := steps + 2;
  steps := steps + (1 + Digits(total - diff));
  IntToStringDigits(total - diff);
  output := IntToString(total - diff);
}

import opened Prelude
