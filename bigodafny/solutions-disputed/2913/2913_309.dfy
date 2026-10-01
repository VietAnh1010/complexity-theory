// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve runs `while i <= n && !flag` with an inner `while j <= n &&
//     !flag`; the first i that satisfies i*j > n with j | i is j = i near
//     sqrt(n), so the cost is about sqrt(n) * n, i.e. n**1.5, which is
//     outside the vocabulary and below O(n**2). The Python has the same
//     loops with flag guards and no break, so the label overstates both.
//
//   how this label could be wrong, and what to check:
//     The label assumes both loops run to x. Check the exit: the inner
//     loop `while j <= n && !flag` has no early break before flag is set,
//     and flag is set first at i about sqrt(n) + 1 (where j = i gives i*j
//     > n), so the outer loop stops after about sqrt(n) rounds of n steps
//     each.
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
