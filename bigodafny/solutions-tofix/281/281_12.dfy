// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-batch-02
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     no := no[j := iv] (and the modulo-branch update) sit inside the
//     doubly-nested oi/j loops, so each seq update copies all n entries
//     across an O(n**2) iteration count, giving O(n**3) per convergence
//     pass; Python's no[j] = ... is an O(1) list index assignment giving
//     O(n**2) per pass as the O(n**2) label assumes, so the label fits the
//     Python and this Dafny is a cubic-in-n translation regression.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 51, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": ["IntToString"], "loop_depth": 3,
//     "loops": 4, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 389_A. Fox and Number Game  (problem 281, solution 281_12)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = eval(input())
// no = list(map(eval,input().split()))
// while True:
//     flag = False
//     for i in no:
//         if i<=0:
//             continue
//         for j in range(n):
//             if no[j]>i:
//                 flag = True
//                 if no[j]%i == 0:
//                     no[j] = i
//                 else:
//                     no[j] = no[j]%i
//     if flag == False:
//         break
// # print(no)
// sum = 0
// for i in no:
//     sum += i
// print(int(sum))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
  decreases *
{
  var no := a_list;
  var flag := true;
  while flag
    invariant |no| == n
    decreases *
  {
    flag := false;
    var oi := 0;
    while oi < n
      invariant 0 <= oi <= n
      invariant |no| == n
      decreases n - oi
    {
      var iv := no[oi];
      if iv > 0 {
        var j := 0;
        while j < n
          invariant 0 <= j <= n
          invariant |no| == n
          decreases n - j
        {
          if no[j] > iv {
            flag := true;
            if no[j] % iv == 0 {
              no := no[j := iv];
            } else {
              no := no[j := no[j] % iv];
            }
          }
          j := j + 1;
        }
      }
      oi := oi + 1;
    }
  }
  var total := 0;
  var k := 0;
  while k < |no|
    decreases |no| - k
  {
    total := total + no[k];
    k := k + 1;
  }
  output := IntToString(total);
}
