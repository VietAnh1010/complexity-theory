// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-02
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     s := s[j := s[j] + s[i]] inside the while i<j loop is a seq update
//     copying all of s on up to n iterations, giving O(n**2); Python's
//     s[j] += s[i] is an O(1) list index update, so O(nlogn) (SortInts
//     plus a linear scan) is right for the Python and wrong for this
//     Dafny.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 24, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": ["SortInts"], "uses_map":
//     false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 158_B. Taxi  (problem 223, solution 223_3085)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = list(map(int, input().split()))
// 
// s.sort()
// 
// i, j = 0, len(s)-1
// res = 0
// 
// while i<j:
//     if s[i]+s[j]<=4:
//         s[j] += s[i]
//         i += 1
//     else:
//         j -= 1
//         res += 1
//         
// print(res+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var s := SortInts(a_list);
  var i := 0;
  var j := |s| - 1;
  var res := 0;
  while i < j
    invariant 0 <= i
    invariant j < |s|
    invariant i <= j + 1
    decreases j - i
  {
    if s[i] + s[j] <= 4 {
      s := s[j := s[j] + s[i]];
      i := i + 1;
    } else {
      j := j - 1;
      res := res + 1;
    }
  }
  output := IntToString(res + 1);
}
