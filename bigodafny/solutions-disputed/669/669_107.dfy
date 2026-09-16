// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-05
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny never calls SortInts (facts.sorts is empty) and instead
//     finds mn/mx and then counts occurrences of mn/mx in two separate
//     O(n) passes, giving O(n) total. Python's s.sort() runs on the raw,
//     arbitrary-order list s before min/max are taken via a=min(s),
//     b=max(s), a real O(n log n) cost that the label reflects, so the
//     omitted sort is the translation's dropped cost.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 31, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 459_B. Pashmak and Flowers  (problem 669, solution 669_107)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x=int(input())
// s=[int(i) for i in input().split()]
// s.sort()
// a=min(s)
// b=max(s)
// if a==b:
//     print(0,int(x*(x-1)/2))
// else:
//     A=0
//     B=0
//     for i in s:
//         if i==a:
//             A+=1
//         if i==b:
//             B+=1
//     print(b-a,int(A*B))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| > 0
{
  var mn := a_list[0];
  var mx := a_list[0];
  var i := 1;
  while i < |a_list|
    decreases |a_list| - i
  {
    if a_list[i] < mn { mn := a_list[i]; }
    if a_list[i] > mx { mx := a_list[i]; }
    i := i + 1;
  }
  if mn == mx {
    output := "0 " + IntToString(n * (n - 1) / 2);
  } else {
    var cntA := 0;
    var cntB := 0;
    i := 0;
    while i < |a_list|
      decreases |a_list| - i
    {
      if a_list[i] == mn { cntA := cntA + 1; }
      if a_list[i] == mx { cntB := cntB + 1; }
      i := i + 1;
    }
    output := IntToString(mx - mn) + " " + IntToString(cntA * cntB);
  }
}
