// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r2-02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Resolved by review with the problem statement: 1 <= a_i <= 100, so
//     the inner loop bounded by x/2 runs at most fifty times regardless of
//     n. The row is O(n) in both Dafny and Python, not O(n**2).
//
//   how this label could be wrong, and what to check:
//     The label assumes the inner loop grows with n. Read the Input
//     section of the problem statement: it caps a_i at 100 while n reaches
//     5*10^4, so the inner bound is a constant. If a later revision of the
//     problem lets a_i scale with n, the O(n**2) label stands; as written
//     it does not. Sibling 342_86 carries O(n) for the same shape and is
//     the correct one.
//
//   structural facts (deterministic, from labelaudit.py):
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
