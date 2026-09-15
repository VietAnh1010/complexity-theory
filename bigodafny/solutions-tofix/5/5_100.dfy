// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r2-01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loop `while m > k { m := m - k; k := k + 1; }` terminates
//     once the triangular number k(k+1)/2 passes n, giving Theta(sqrt(n))
//     iterations rather than n; the Python has the byte-identical
//     while-loop with the same k increment, so it is Theta(sqrt(n)) too,
//     meaning the label is wrong about the Python it was measured on.
//
//   how this label could be wrong, and what to check:
//     The label assumes the loop runs on the order of n times, but k grows
//     by 1 every pass while m falls by k, so it stops once k(k+1)/2
//     exceeds n -- Theta(sqrt(n)) iterations, not n. Instrument the `while
//     m > k` loop with a counter for a large n (e.g. n=10**6) and check
//     the count lands near sqrt(2n) (~1414) rather than near n; if so the
//     tight class is O(sqrt(n)), which is outside this dataset's
//     vocabulary.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 13, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 622_A. Infinite Sequence  (problem 5, solution 5_100)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// k=1
// while(n>k):
//    n-=k
//    k+=1
// print(n)
//    
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var m, k := n, 1;
  while m > k
    decreases m - k
  {
    m := m - k;
    k := k + 1;
  }
  output := IntToString(m) + "\n";
}
