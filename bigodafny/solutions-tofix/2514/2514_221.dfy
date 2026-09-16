// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-19
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     arr := arr[i := kk] runs inside the while loop up to n times and
//     each seq update copies all |arr|=n elements, giving O(n**2);
//     Python's a[i]=k is an O(1) list write so the Python stays O(nlogn)
//     after the sort as labeled.
//
//   how this label could be wrong, and what to check:
//     The label assumes the adjustment loop costs O(n) total as it does in
//     Python. Open the while i<|arr| loop and confirm arr := arr[i := kk]
//     is a seq update executed on nearly every iteration (since kk is the
//     minimum, most arr[i] exceed it); each such update copies the full
//     |arr|=n seq, so the true cost is O(n**2), dominating the O(nlogn)
//     sort.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 33, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "MinSeq", "SumSeq"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts":
//     ["Sort"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 1084_B. Kvass and the Fair Nut  (problem 2514, solution 2514_221)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = list(map(int,input().split()))
// s = n[1]
// n = n[0]
// a = list(map(int,input().split()))
// 
// a = sorted(a,reverse = True)
// k = min(a)
// su = 0
// if s > sum(a):
//     print(-1)
// else:
//     for i in range(len(a)):
//         if a[i] > k:
//             su += (a[i]-k)
//             a[i] = k
//             if su >= s:
//                 break
//     if su < s:
//         k = (n*k-(s-su))//n
//         print(k)
//     else:
//         print(k)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>) returns (output: string)
  requires |c_list| >= 1
  requires a >= 1
{
  var arr := Sort(c_list, (x: int, y: int) => x > y);
  var kk := MinSeq(c_list);
  var su := 0;
  var total := SumSeq(c_list);
  if b > total {
    output := "-1";
  } else {
    var i := 0;
    while i < |arr| && su < b
      invariant 0 <= i <= |arr|
      invariant |arr| == |c_list|
      decreases |arr| - i
    {
      if arr[i] > kk {
        su := su + (arr[i] - kk);
        arr := arr[i := kk];
      }
      i := i + 1;
    }
    if su < b {
      var res := FloorDiv(a * kk - (b - su), a);
      output := IntToString(res);
    } else {
      output := IntToString(kk);
    }
  }
}
