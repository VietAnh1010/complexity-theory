// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r2-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Each matrix row is read only at fixed indices l[0]..l[3] (A, B, C,
//     D) per the `requires |matrices[i]| >= 4` precondition, with O(1)
//     arithmetic and string selection per test case and no loop over row
//     width; the outer loop runs |matrices|=n times, so the true class is
//     O(n), and sibling 1170_62 solving the identical problem is correctly
//     labeled O(n).
//
//   how this label could be wrong, and what to check:
//     The label O(n*m) implies cost scaling with row width m, but check
//     that the Dafny only ever indexes l[0], l[1], l[2], l[3] -- four
//     fixed positions -- and never loops over the row itself. If
//     confirmed, m does not enter the cost and the label should be O(n),
//     matching sibling 1170_62 which solves the identical 'Huge Boxes of
//     Animal Toys' problem with the same structure and that label.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 32, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 1, "loops":
//     1, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1425_H. Huge Boxes of Animal Toys  (problem 1170, solution 1170_10)
// time complexity: O(n*m)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for _ in range(t):
//     l=list(map(int,input().split()))
//     a=[0]*4
//     if(l[0]+l[3]!=0):
//         a[0]=1
//         a[3]=1
//     if(l[1]+l[2]!=0):
//         a[1]=1
//         a[2]=1
//     if((l[1]+l[0])%2==0):
//         a[0]=0
//         a[1]=0
//     else:
//         a[2]=0
//         a[3]=0
//     for x in a:
//         if(x==0):
//             print("Tidak",end=" ")
//         else:
//             print("Ya",end=" ")
//     print(" ")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrices: seq<seq<int>>) returns (output: string)
  requires forall i :: 0 <= i < |matrices| ==> |matrices[i]| >= 4
{
  var parts: seq<string> := [];
  var i := 0;
  while i < |matrices|
    invariant 0 <= i <= |matrices|
    decreases |matrices| - i
  {
    var l := matrices[i];
    var a0 := if l[0] + l[3] != 0 then 1 else 0;
    var a3 := if l[0] + l[3] != 0 then 1 else 0;
    var a1 := if l[1] + l[2] != 0 then 1 else 0;
    var a2 := if l[1] + l[2] != 0 then 1 else 0;
    if (l[1] + l[0]) % 2 == 0 {
      a0 := 0;
      a1 := 0;
    } else {
      a2 := 0;
      a3 := 0;
    }
    var w0 := if a0 == 0 then "Tidak" else "Ya";
    var w1 := if a1 == 0 then "Tidak" else "Ya";
    var w2 := if a2 == 0 then "Tidak" else "Ya";
    var w3 := if a3 == 0 then "Tidak" else "Ya";
    parts := parts + [w0 + " " + w1 + " " + w2 + " " + w3 + "  \n"];
    i := i + 1;
  }
  output := Join(parts, "");
}
