// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve runs a linear pass and then for each element a_i another loop
//     to a_i/2, so cost is O(n * max a_i) with a value term, not O(n**2);
//     the Python has the same inner range(2, x // 2 + 1).
//
//   how this label could be wrong, and what to check:
//     The label assumes two input-size loops, but the inner loop runs to
//     x/2 where x is the VALUE a_i. Check `while y <= x / 2` in Solve and
//     the Python's range(2, x // 2 + 1); the statement caps a_i at 100 but
//     that is not a literal in the source.
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

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| >= 1
{
  var s := 0;
  var minEl := a_list[0];
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    s := s + a_list[i];
    if a_list[i] < minEl { minEl := a_list[i]; }
    i := i + 1;
  }
  var diff := 0;
  i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    var x := a_list[i];
    if x != minEl {
      var y := 2;
      while y <= x / 2
        decreases x - y
      {
        if x % y == 0 {
          var newX := x / y;
          var newMin := minEl * y;
          var newDiff := x + minEl - newX - newMin;
          if newDiff > diff { diff := newDiff; }
        }
        y := y + 1;
      }
    }
    i := i + 1;
  }
  output := IntToString(s - diff);
}
