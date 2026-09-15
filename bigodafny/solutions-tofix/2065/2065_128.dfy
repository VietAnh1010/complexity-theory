// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : both
//   confidence     : medium
//   auditor        : labelaudit-batch-15
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     The outer while loop runs about sqrt(2n) times (bounded by the
//     binary-search-computed lim), and each iteration itself runs an inner
//     binary search of O(log n) steps to emulate math.sqrt(c), giving
//     Dafny cost O(sqrt(n) log n); the Python's for i in
//     range(1,int(math.sqrt(a))) is the same sqrt(n) outer count but each
//     iteration calls the O(1) hardware math.sqrt, giving Python cost
//     O(sqrt(n)), so neither matches the O(n) label and the translation
//     itself adds a log(n) factor Python does not pay.
//
//   how this label could be wrong, and what to check:
//     The label assumes cost scales with the value n, but the outer loop
//     only runs until i reaches lim ~ sqrt(2n) (a binary search replacing
//     math.sqrt), so no construct touches n items directly. Count the
//     outer loop's iteration bound (lim, derived from a binary search on
//     mid*mid<=a) against sqrt(n) to confirm it is sublinear in the value
//     n, not linear.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 50, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 2, "loops": 3,
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

  var lo := 0;
  var hi := a + 1;
  while lo < hi
    decreases hi - lo
  {
    var mid := (lo + hi + 1) / 2;
    if mid * mid <= a {
      lo := mid;
    } else {
      hi := mid - 1;
    }
  }
  var lim := lo;

  var i := 1;
  while i < lim
    decreases lim - i
  {
    var c := a - i * i - i;
    if c >= 0 {
      var dlo := 0;
      var dhi := c + 1;
      while dlo < dhi
        decreases dhi - dlo
      {
        var mid2 := (dlo + dhi + 1) / 2;
        if mid2 * mid2 <= c {
          dlo := mid2;
        } else {
          dhi := mid2 - 1;
        }
      }
      var d := dlo;
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
