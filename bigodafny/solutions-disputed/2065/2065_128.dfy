// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : both
//   confidence     : medium
//   auditor        : labelaudit-r3d-06
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     The Python loops about sqrt(2n) times with math.sqrt, so O(sqrt n),
//     while the Dafny's outer loop runs sqrt(2n) times with an inner
//     binary-search sqrt, giving O(sqrt(n) log n) in the VALUE n; neither
//     is the labelled O(n), and the Dafny additionally reimplements
//     math.sqrt.
//
//   how this label could be wrong, and what to check:
//     The label O(n) treats n as a linear loop bound, but the outer loop
//     `while i < lim` runs lim ~ sqrt(2n) times, and the Dafny runs an
//     inner binary search for the integer sqrt at each step (log factor),
//     where the Python calls math.sqrt in O(1). Check the Python `for i in
//     range(1,int(math.sqrt(a)))` to confirm O(sqrt n), and the Dafny
//     inner `dlo < dhi` loop to confirm the extra log.
//
//   structural facts (deterministic, from label_audit.py):
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
