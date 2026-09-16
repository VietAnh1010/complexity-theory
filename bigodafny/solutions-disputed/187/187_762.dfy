// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-01-sonnet
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     arr is a seq<int>, and inside the nested while loops over i and j
//     (O(n^2) iterations), every triggered swap performs `arr := arr[i :=
//     arr[j]]` and `arr := arr[j := tmp]`, each an O(n) full-sequence
//     copy, so the real cost is n^2 trigger iterations times an O(n) copy,
//     worse than quadratic and only approximable by the largest available
//     vocabulary entry O(n**2); Python's `t=list[i]; list[i]=list[j];
//     list[j]=t` performs the same swap with O(1) in-place writes, which
//     is why O(n**2) is correct for the Python but not for this seq-based
//     translation.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 31, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 984_A. Game  (problem 187, solution 187_762)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def sort(n,a):
//     list = a
//     for i in range(0,n):
//         for j in range(0,n):
//             if(list[i]>list[j]):
//                 t = list[i]
//                 list[i] = list[j]
//                 list[j] = t
//     return list
// def erase(n,a):
//     temp=1
//     list = sort(n,a)
//     t=0
//     print(a[(n)//2])
// n = int(input())
// a = [int(i) for i in input().split()]
// erase(n,a)
//             
//             
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
  requires n >= 1
{
  var arr := a_list;
  var i := 0;
  while i < n
    invariant 0 <= i
    invariant |arr| == n
    decreases n - i
  {
    var j := 0;
    while j < n
      invariant 0 <= j
      invariant |arr| == n
      decreases n - j
    {
      if arr[i] > arr[j] {
        var tmp := arr[i];
        arr := arr[i := arr[j]];
        arr := arr[j := tmp];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  var idx := n / 2;
  output := IntToString(arr[idx]);
}
