// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(logn)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-01-sonnet
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The translated binary search `while lo < hi` halves the [0, num+2)
//     range each iteration to recover the integer square root, giving
//     O(log(num)) iterations, while the Python it replaces computes the
//     same value with a single O(1) call to math.sqrt, so O(1) held for
//     the Python but not for this Dafny loop.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 27, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 622_A. Infinite Sequence  (problem 5, solution 5_25)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// number = input()
// current = 0
// num = int(number)
// D = math.sqrt(1 + 8*num)
// n = ( D - 1 )/2
// n = int(n)
// summa = n*(n+1)/2
// if num == summa:
// 	n-=1
// 	summa = n*(n+1)/2
// if num>summa:
// 	num -= summa
// num = int (num)
// print (num)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var num := n;
  var m := 1 + 8 * num;
  // find largest k >= 0 with (2k+1)^2 <= m  (== floor((sqrt(m)-1)/2))
  var lo := 0;
  var hi := num + 2;
  while lo < hi
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if (2 * mid + 1) * (2 * mid + 1) <= m {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  var k := lo - 1;
  var summa := k * (k + 1) / 2;
  if num == summa {
    k := k - 1;
    summa := k * (k + 1) / 2;
  }
  var result := num - summa;
  output := IntToString(result);
}
