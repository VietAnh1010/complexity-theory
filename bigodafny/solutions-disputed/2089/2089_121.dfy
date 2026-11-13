// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny's two `while` loops run from 1 to a - b and from a - b + 1
//     to a, n iterations in total with an O(1) append each, so the cost is
//     O(n); the Python's two sequential `for` loops are the same.
//
//   how this label could be wrong, and what to check:
//     The label multiplies n and k, but the two loops are sequential and
//     together run n times: `range(1, n-k)` then `range(n-k+1, n+1)`.
//     Check that neither loop is nested in the other; the cost is linear
//     in the value n.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 23, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["JoinInts"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 361_B. Levko and Permutation  (problem 2089, solution 2089_121)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=map(int,input().split())
// if n==k:
//     print(-1)
// else:
//     a=[]
//     a.append(n-k)
//     for i in range(1,n-k):
//         a.append(i)
//     for j in range(n-k+1,n+1):
//         a.append(j)
//     print(*a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  if a == b {
    output := "-1\n";
  } else {
    var lst: seq<int> := [a - b];
    var i := 1;
    while i < a - b
    {
      lst := lst + [i];
      i := i + 1;
    }
    var j := a - b + 1;
    while j <= a
    {
      lst := lst + [j];
      j := j + 1;
    }
    output := JoinInts(lst, " ") + "\n";
  }
}
