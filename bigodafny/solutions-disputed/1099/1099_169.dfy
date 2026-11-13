// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python sorts the scores and counts distinct runs, O(n log n) as
//     labelled; the Dafny builds `s: set<int>` of nonzero scores in one
//     pass and outputs `|s|`, O(n), replacing the sort.
//
//   how this label could be wrong, and what to check:
//     The label comes from the Python's `a.sort()` followed by a count of
//     changes between neighbours. Check that the Dafny never sorts: it
//     inserts nonzero scores into a set and returns its size, O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 14, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": true, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": true}
// --------------------------------------------------------------------

// 937_A. Olympiad  (problem 1099, solution 1099_169)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// a.sort()
// if (a[0]!=0): res = 1
// else: res = 0
// b = a[0]
// for i in range(len(a)):
//     if (a[i]!=b): res+=1
//     b = a[i]
// print(str(res))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var s: set<int> := {};
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    if a_list[i] != 0 { s := s + {a_list[i]}; }
    i := i + 1;
  }
  output := IntToString(|s|);
}

