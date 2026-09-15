// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-12
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     `x` and `y` are bounded by 0<=x,y<=7 per the statement, so the Dafny
//     inner loops `while j < i` (bounded by x) and `while j < i+y+1`
//     (bounded by y) each do at most 7 O(1) steps; the outer `while i <
//     |arr| && !found` loop is the only part scaling with n, and Python's
//     identical `range(i-x,i)`/`range(i+1,i+y+1)` loops are just as
//     bounded, making both sources O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes the inner scans over x and y grow with n. Check
//     the problem constraint `0 <= x, y <= 7`: since x and y are each
//     capped at 7, the `while j < i` and `while j < i + y + 1` loops run
//     at most 7 iterations regardless of n, so the outer `while i < |arr|`
//     loop's O(n) iterations dominate and the true cost is O(n), not
//     O(n**2).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 48, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 3, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1199_A. City Day  (problem 1820, solution 1820_122)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,x,y=map(int,input().split())
// a=list(map(int,input().split()))
// 
// ind=0
// 
// for i in range(len(a)):
//     
//     chx=1
//     chy=1
//     
//     for j in range(i-x,i):
//         if(j>=0):
//             if(a[i]>=a[j]):
//                 chx=0
//                 break
//         
//     for j in range(i+1,i+y+1):
//         if(j<n):
//             if(a[i]>=a[j]):
//                 chy=0
//                 break
//         
//     if(chx==1 and chy==1):
//         ind=i
//         break
// 
// print(ind+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string)
  requires a <= |d_list|
{
  var n := a;
  var x := b;
  var y := c;
  var arr := d_list;
  var ind := 0;
  var i := 0;
  var found := false;
  while i < |arr| && !found
    decreases !found, |arr| - i
  {
    var chx := true;
    var chy := true;
    var j := i - x;
    while j < i
      decreases i - j
    {
      if j >= 0 && arr[i] >= arr[j] {
        chx := false;
        j := i;
      } else {
        j := j + 1;
      }
    }
    j := i + 1;
    while j < i + y + 1
      decreases i + y + 1 - j
    {
      if j < n && arr[i] >= arr[j] {
        chy := false;
        j := i + y + 1;
      } else {
        j := j + 1;
      }
    }
    if chx && chy {
      ind := i;
      found := true;
    } else {
      i := i + 1;
    }
  }
  output := IntToString(ind + 1);
}
