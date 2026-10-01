// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve makes one loop over the rectangles with comparisons of row[0]
//     and row[1] only; the Python's max(dimensions[i]) runs over exactly
//     two numbers, so both are O(n) and the O(n*m) label names a dimension
//     that does not exist.
//
//   how this label could be wrong, and what to check:
//     The label assumes variable rectangle width m. Check the statement:
//     each line is exactly two integers w_i, h_i; Solve reads only row[0]
//     and row[1] and the Python's max/min over dimensions[i] act on a
//     two-element list.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 26, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1008_B. Turn the Rectangles  (problem 396, solution 396_361)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// dimensions = []
// flag = 1
// 
// while n > 0:
//     dimensions.append(list(map(int, input().split())))
//     n -= 1
// 
// maximum = max(dimensions[0])
// 
// for i in range(1, len(dimensions)):
//     if maximum >= max(dimensions[i]):
//         maximum = max(dimensions[i])
//         continue
//     elif maximum >= min(dimensions[i]):
//         maximum = min(dimensions[i])
//         continue
//     else:
//         flag = 0
//         break
// 
// if flag:
//     print("YES")
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, rectangles: seq<seq<int>>) returns (output: string)
  requires |rectangles| >= 1
  requires forall k :: 0 <= k < |rectangles| ==> |rectangles[k]| >= 2
{
  var maxV := if rectangles[0][0] > rectangles[0][1] then rectangles[0][0] else rectangles[0][1];
  var flag := true;
  var i := 1;
  while i < |rectangles| && flag
    decreases |rectangles| - i
  {
    var row := rectangles[i];
    var mx := if row[0] > row[1] then row[0] else row[1];
    var mn := if row[0] < row[1] then row[0] else row[1];
    if maxV >= mx {
      maxV := mx;
    } else if maxV >= mn {
      maxV := mn;
    } else {
      flag := false;
    }
    i := i + 1;
  }
  output := if flag then "YES" else "NO";
}
