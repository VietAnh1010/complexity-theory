// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-08
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The single loop over values_list reads row[0] and row[1] and never
//     walks a row, so Solve is O(n) in the number of commands. The Python
//     splits each line into exactly three ints, so it pays constant per
//     row and is O(n) too; the label is wrong, not the translation.
//
//   how this label could be wrong, and what to check:
//     The label assumes each command row has a variable width m. Check the
//     problem statement: each line is exactly three integers ti, xi, yi,
//     so the row width is a constant; if rows could be ragged the label
//     would stand.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 25, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 245_A. System Administrator  (problem 2719, solution 2719_94)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// num=eval(input())
// alist=[]
// for i in range(num):
//     a=input()
//     b=a.split()
//     c=[int(x) for x in b]
// 
//     alist.append(c)
// 
// 
// geshua=0
// geshub=0
// zongshua=0
// zongshub=0
// for k in alist:
//     if k[0]==1:
//         geshua=geshua+1
//         zongshua=zongshua+k[1]
//     else:
//         geshub=geshub+1
//         zongshub=zongshub+k[1]
// 
// if zongshua>=geshua*5:
//     print("LIVE")
// else:
//     print('DEAD')
// if zongshub>=geshub*5:
//     print("LIVE")
// else:
//     print('DEAD')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values_list: seq<seq<int>>) returns (output: string)
{
  var geshua := 0; var geshub := 0; var zongshua := 0; var zongshub := 0;
  var i := 0;
  while i < |values_list|
    invariant 0 <= i <= |values_list|
  {
    var row := values_list[i];
    if |row| >= 2 {
      if row[0] == 1 {
        geshua := geshua + 1;
        zongshua := zongshua + row[1];
      } else {
        geshub := geshub + 1;
        zongshub := zongshub + row[1];
      }
    }
    i := i + 1;
  }
  var line1 := if zongshua >= geshua * 5 then "LIVE" else "DEAD";
  var line2 := if zongshub >= geshub * 5 then "LIVE" else "DEAD";
  output := line1 + "\n" + line2;
}
