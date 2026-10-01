// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r4-d01
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python recomputes sum(X[i:n]) for every i (a slice copy plus
//     sum, O(n) each), so it is O(n**2) as labelled. The Dafny fills
//     total[i] = total[i+1] + a_list[i] once in a single backward loop and
//     reuses it in the second loop, with O(1) seq updates, so it is O(n):
//     the translation replaced the algorithm with a prefix-sum, landing a
//     class faster.
//
//   how this label could be wrong, and what to check:
//     The label was measured on a Python that evaluates `sum(X[i:n])`
//     inside its loop, which is quadratic. Check that the Dafny replaces
//     that with a precomputed suffix table `total` filled in a separate
//     loop; if so the Dafny is a better class than the Python.
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
