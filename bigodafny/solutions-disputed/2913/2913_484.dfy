// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop `while a <= n && !found` increments a until a * a > n,
//     which happens after about sqrt(n) iterations, so the tight cost is
//     O(sqrt n), below the labelled O(n) and outside the vocabulary. The
//     Python's range(1, x+1) loop with `if ((a*a)>x)` returns at the same
//     point.
//
//   how this label could be wrong, and what to check:
//     The label assumes the loop runs to n. Check the exit condition
//     inside the loop: `if a * a > n` sets found, so the loop stops at a
//     about sqrt(n) + 1 and never reaches n; if the loop really ran to n
//     for typical x the label would stand.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 24, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1088_A. Ehab and another construction problem  (problem 2913, solution 2913_484)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def Calculo_Brute_Force(x):
//     
//     for a in range(1,x+1):
//             if ((a*a)>x) :
//                 print (a,a)
//                 return(a,a)
//     
//     print(-1)
//     return(-1)
// 
// Calculo_Brute_Force(int(input()))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var a := 1;
  var found := false;
  var ans := 0;
  while a <= n && !found
    invariant 1 <= a
    decreases n - a, if found then 0 else 1
  {
    if a * a > n {
      ans := a;
      found := true;
    } else {
      a := a + 1;
    }
  }
  if found {
    output := IntToString(ans) + " " + IntToString(ans) + "\n";
  } else {
    output := "-1\n";
  }
}
