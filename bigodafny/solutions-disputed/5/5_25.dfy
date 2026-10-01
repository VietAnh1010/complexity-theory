// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : other
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r3d-01
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny replaces the Python's single math.sqrt(1 + 8*num) with a
//     binary search loop over [0, n+2], costing O(log n) in the input
//     value n, while the Python is O(1) per call; this is a reimplemented
//     library call.
//
//   how this label could be wrong, and what to check:
//     The label assumes constant work, which matches the Python's single
//     math.sqrt call. Check Solve's binary search (lo, hi := 0, num+2): it
//     runs about log2(n) iterations in the VALUE n, standing in for the
//     one math.sqrt call in the Python.
//
//   structural facts (deterministic, from label_audit.py):
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
