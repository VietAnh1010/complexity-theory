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

include "../../prelude.dfy"
import opened Prelude

ghost function PosPref342(a: seq<int>, i: nat): nat
  requires i <= |a|
  decreases i
{
  if i == 0 then 0 else PosPref342(a, i - 1) + (if a[i - 1] > 0 then a[i - 1] else 0)
}

lemma SelfLeSq(j: int)
  requires j >= 1
  ensures j <= j * j
{
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| >= 1
  ensures steps <= 25 * |a_list| + 12 * PosPref342(a_list, |a_list|) + 30 + |output|
{
  steps := 1;
  var total := 0;
  var idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant steps == 1 + 4 * idx
    decreases |a_list| - idx
  {
    total := total + a_list[idx];
    idx := idx + 1;
    steps := steps + 4;
  }
  var m := a_list[0];
  idx := 0;
  steps := steps + 2;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant steps == 3 + 4 * |a_list| + 5 * idx
    decreases |a_list| - idx
  {
    if a_list[idx] < m { m := a_list[idx]; }
    idx := idx + 1;
    steps := steps + 5;
  }
  var diff := 0;
  idx := 0;
  steps := steps + 2;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant steps <= 5 + 9 * |a_list| + 12 * idx + 12 * PosPref342(a_list, idx)
    decreases |a_list| - idx
  {
    var v := a_list[idx];
    var j := 1;
    ghost var P: nat := if v > 0 then v else 0;
    ghost var s1 := steps;
    while j * j <= v
      invariant 1 <= j
      invariant j - 1 <= P
      invariant steps <= s1 + 12 * (j - 1)
      decreases v - j * j
    {
      SelfLeSq(j);
      if v % j == 0 {
        var term := v + m - v / j - m * j;
        if term > diff { diff := term; }
      }
      j := j + 1;
      steps := steps + 12;
    }
    idx := idx + 1;
    steps := steps + 12;
  }
  IntToStringDigits(total - diff);
  output := IntToString(total - diff);
  steps := steps + Digits(total - diff);
}
