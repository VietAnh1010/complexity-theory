// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r3-04
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny precomputes suffix sums in `total` in one O(n) loop, then
//     the main loop reads total[i] in O(1) with O(1) seq updates, so it is
//     O(n). The Python's sum(X[i:n]) per iteration is O(n**2) as labelled,
//     so the Dafny replaced the algorithm with a faster one.
//
//   how this label could be wrong, and what to check:
//     The label was measured on a Python that calls sum(X[i:n]) inside the
//     loop, which copies and sums n-i items each step, so the Python is
//     quadratic. Open the Dafny and check that the first loop builds the
//     suffix-sum seq `total` once with `total[i := total[i+1] +
//     a_list[i]]`, and that the second loop only reads total[i] in O(1).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 33, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 859_C. Pie Rules  (problem 647, solution 647_11)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// X = list(map(int, input().split()))
// 
// ali = [None]*(n+1)
// bob = [None]*(n+1)
// 
// ali[n] = 0
// bob[n] = 0
// 
// for i in range(n-1, -1, -1):
// 	bob[i] = max(bob[i+1], ali[i+1]+X[i])
// 	ali[i] = sum(X[i:n]) - bob[i]
// 	
// #print(ali)
// #print(bob)
// 
// print(ali[0], bob[0], sep=' ')
// 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n >= 1
  requires |a_list| == n
{
  // total[i] = sum of a_list[i..n-1]
  var total := seq(n + 1, _ => 0);
  var i := n - 1;
  while i >= 0
    invariant -1 <= i <= n - 1
    invariant |total| == n + 1
    decreases i
  {
    total := total[i := total[i+1] + a_list[i]];
    i := i - 1;
  }
  var ali := seq(n + 1, _ => 0);
  var bob := seq(n + 1, _ => 0);
  i := n - 1;
  while i >= 0
    invariant -1 <= i <= n - 1
    invariant |total| == n + 1
    invariant |ali| == n + 1
    invariant |bob| == n + 1
    decreases i
  {
    var bv := if bob[i+1] > ali[i+1] + a_list[i] then bob[i+1] else ali[i+1] + a_list[i];
    bob := bob[i := bv];
    ali := ali[i := total[i] - bv];
    i := i - 1;
  }
  output := IntToString(ali[0]) + " " + IntToString(bob[0]);
}
