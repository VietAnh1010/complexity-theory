// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r4-d01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The outer loop runs |a_list| times and the inner loop `while y <= x
//     / 2` runs to half of the element value x, so the cost is O(n * max
//     a_i), a value term the label's variables do not account for; the cap
//     1 <= a_i <= 100 is a statement cap, not a source literal. The Python
//     has the same range(2, x // 2 + 1) loop.
//
//   how this label could be wrong, and what to check:
//     The label reads the nested loops as two list-size loops. Check the
//     inner `while y <= x / 2` loop: its bound is the element value x, not
//     a list length, so the label's n does not account for it.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 39, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 3, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1113_B. Sasha and Magnetic Machines  (problem 342, solution 342_149)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// 
// n = int(input())
// arr_str = input().split()
// 
// arr = [int(x) for x in arr_str]
// 
// 
// min_el = arr[0]
// s = 0
// 
// for x in arr:
//     s += x
//     if x < min_el:
//         min_el = x
// 
// diff = 0
// 
// 
// for x in arr:
//     if x == min_el:
//         continue
//     for y in range(2, x // 2 + 1):
//         if x % y == 0:
//             new_x = x // y
//             new_min = min_el*y
//             new_diff = x + min_el - new_x - new_min
//             if new_diff > diff:
//                 diff = new_diff
// 
// print(s - diff)
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

ghost function PosSum(a: seq<int>, k: nat): nat
  requires k <= |a|
  decreases k
{
  if k == 0 then 0 else PosSum(a, k - 1) + (if a[k - 1] > 0 then a[k - 1] else 0)
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| >= 1
  ensures steps <= 20 * |a_list| + 16 * PosSum(a_list, |a_list|) + 2 * |output| + 20
{
  steps := 3;
  var s := 0;
  var minEl := a_list[0];
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps == 3 + 6 * i
    decreases |a_list| - i
  {
    s := s + a_list[i];
    if a_list[i] < minEl { minEl := a_list[i]; }
    i := i + 1;
    steps := steps + 6;
  }
  var diff := 0;
  i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps <= 3 + 6 * |a_list| + 14 * i + 16 * PosSum(a_list, i)
    decreases |a_list| - i
  {
    ghost var st0 := steps;
    var x := a_list[i];
    steps := steps + 4;
    if x != minEl {
      var y := 2;
      steps := steps + 2;
      while y <= x / 2
        invariant 2 <= y && (y == 2 || y <= x / 2 + 1)
        invariant steps <= st0 + 6 + 16 * (y - 2)
        decreases x - y
      {
        if x % y == 0 {
          var newX := x / y;
          var newMin := minEl * y;
          var newDiff := x + minEl - newX - newMin;
          if newDiff > diff { diff := newDiff; }
        }
        y := y + 1;
        steps := steps + 16;
      }
      assert y - 2 <= (if x > 0 then x else 0);
      steps := steps + 1;
    }
    i := i + 1;
    steps := steps + 2;
    assert PosSum(a_list, i) == PosSum(a_list, i - 1) + (if a_list[i - 1] > 0 then a_list[i - 1] else 0);
  }
  output := IntToString(s - diff);
  IntToStringDigits(s - diff);
  steps := steps + 2 + Digits(s - diff);
}
