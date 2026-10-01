// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-16
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Both loops are bounded by the value n but exit through flag at the
//     first pair with i % j == 0 and i * j > n, which first occurs at i =
//     floor(sqrt n) + 1, j = i, so the outer loop completes about sqrt(n)
//     full inner passes of n steps each, about n**1.5 total; the Python
//     has the same early-exit loops, so O(n**2) is a loose upper bound.
//
//   how this label could be wrong, and what to check:
//     The label assumes both loops run to n. Check the exit: the flag is
//     set at the first (i, j) with j dividing i and i*j > n, and since j
//     <= i this needs i > sqrt(n); work n = 100 by hand and count the
//     inner iterations to see that only about sqrt(n) outer rounds each
//     run the full inner loop.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 32, "data_dependent_loops": 2, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1088_A. Ehab and another construction problem  (problem 2913, solution 2913_309)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// flag=0
// for i in range(1,t+1):
//     if flag!=1:
//         for j in range(1,t+1):
//             if flag!=1:
//                 if i%j == 0:
//                     if i*j>t:
//                         if i%j < t:
//                             a,b = i,j
//                             flag=1
// if flag==1:
//     print(a,b)
// else:
//     print("-1")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var flag := false;
  var a := 0;
  var b := 0;
  var i := 1;
  while i <= n && !flag
    invariant 1 <= i
    decreases n - i
  {
    var j := 1;
    while j <= n && !flag
      invariant 1 <= j
      decreases n - j
    {
      if i % j == 0 && i * j > n && i % j < n {
        a := i;
        b := j;
        flag := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  if flag {
    output := IntToString(a) + " " + IntToString(b) + "\n";
  } else {
    output := "-1\n";
  }
}
