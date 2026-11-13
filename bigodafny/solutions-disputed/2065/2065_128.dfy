// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loops i from 1 to `ISqrt(2n)`, about sqrt(2n) iterations,
//     and calls `ISqrt(c)` in each, charged O(log n), so the cost is
//     O(sqrt(n) log n); the Python's loop and `math.sqrt(c)` match.
//
//   how this label could be wrong, and what to check:
//     The label is linear in the value n, but the loop runs i up to
//     sqrt(2n) and takes a square root each time. Check the loop bound
//     `lim := ISqrt(a)` and the inner `ISqrt(c)`; the class is O(sqrt(n)
//     log n), the Python taking `math.sqrt(c)` at the same point.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 26, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 0, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 192_A. Funky Numbers  (problem 2065, solution 2065_128)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #codeforces.com:3.2.5(2.4.0)
// import math
// a=int(input())*2;b=0
// for i in range(1,int(math.sqrt(a))):
//     c=a-i*i-i;d=int(math.sqrt(c))
//     if d*(d+1)==c:b=1
// print("YES")if(b)else print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var a := n * 2;
  var b := 0;

  var lim: int := ISqrt(a);

  var i := 1;
  while i < lim
    decreases lim - i
  {
    var c := a - i * i - i;
    if c >= 0 {
      var d := ISqrt(c);
      if d * (d + 1) == c {
        b := 1;
      }
    }
    i := i + 1;
  }

  if b == 1 {
    output := "YES";
  } else {
    output := "NO";
  }
}
