// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-16
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The while loop in Solve increments a until a * a > n and sets found,
//     which happens at a = floor(sqrt n) + 1, so it runs O(sqrt n)
//     iterations in the value n, not O(n); the Python for-loop breaks out
//     at the same point via return, so the label is loose for both.
//
//   how this label could be wrong, and what to check:
//     The label assumes the loop runs to n. Check the loop condition: it
//     stops at the first a with a * a > n, so for n = 100 count the
//     iterations (11), which is about sqrt(n), not n; if reviewers accept
//     the statement-level worst case rather than the tight class, the
//     label stands.
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
