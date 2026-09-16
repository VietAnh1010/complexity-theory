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
//     IntSqrtFloor is an O(log n) binary search, but the following loop
//     `while i < x && p == 0 { ...; i := i + 1; }` runs up to x =
//     floor(sqrt(n)) times, making the whole method Theta(sqrt(n)) rather
//     than Theta(n); the Python's `for i in range(1, x)` has the identical
//     bound x = floor(sqrt(n)).
//
//   how this label could be wrong, and what to check:
//     The label assumes the search loop scans on the order of n
//     candidates, but it is bounded by x = floor(sqrt(n)), not n, via
//     `while i < x && p == 0`. Instrument the loop counter i for a large n
//     (e.g. n=10**8) and check it tops out near sqrt(n) (~10000) rather
//     than near n; if so the tight class is O(sqrt(n)), and it is the
//     label (measured on the same Python range(1,x) loop) that is wrong,
//     not the translation.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 41, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1184_A1. Heidi Learns Hashing (Easy)  (problem 167, solution 167_177)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n = int(input())
// x = math.floor(math.sqrt(n))
// p = 0
// for i in range(1, x):
// 	if (n-1-i**2-i)%(2*i) == 0 :
// 		print(i,  (n-1-i**2-i)//(2*i))
// 		p = 1
// 		break
// if not p:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
  requires n >= 0
{
  var x := IntSqrtFloor(n);
  var p := 0;
  var result := "";
  var i := 1;
  while i < x && p == 0
    decreases x - i
  {
    var expr := n - 1 - i * i - i;
    if expr % (2 * i) == 0 {
      result := IntToString(i) + " " + IntToString(expr / (2 * i));
      p := 1;
    }
    i := i + 1;
  }
  if p == 0 {
    result := "NO";
  }
  output := result;
}

method IntSqrtFloor(x: int) returns (r: int)
  requires x >= 0
{
  var lo := 0;
  var hi := x + 1;
  while lo < hi
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if mid * mid <= x {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  r := lo - 1;
}
