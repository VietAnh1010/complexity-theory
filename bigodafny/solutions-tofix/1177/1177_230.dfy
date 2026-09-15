// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n+m)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r2-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve runs two separate while loops, one scanning `rectangles` for n
//     iterations and a second scanning `checks` for m iterations, each
//     doing O(1) min/max updates per iteration; n and m are independent
//     parameters (each bounded separately at 200,000 in the problem
//     statement), so the tight class is O(n+m), and the Python's own two
//     separate for-loops over n and m show the identical two-phase linear
//     cost.
//
//   how this label could be wrong, and what to check:
//     The label O(n) omits the second while loop, which scans `checks`
//     (length m) exactly once with the same O(1) per-iteration cost as the
//     first loop over `rectangles`. Check that n and m can vary
//     independently per the problem's two separate bounds (1<=n<=200000 on
//     one line, 1<=m<=200000 on another); if so the true class must
//     include both dimensions as O(n+m), not O(n) alone.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 40, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 785_B. Anton and Classes  (problem 1177, solution 1177_230)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l1=1000000005
// z2=1000000005
// l2=0
// z1=0
// for i in range(0,n):
//      x,y=input().split(" ")
//      x,y=int(x),int(y)
//      l1=min(y,l1)
//      z1=max(z1,x)
// m=int(input())
// for i in range(0,m):
//      x,y=input().split(" ")
//      x,y=int(x),int(y)
//      l2=max(x,l2)
//      z2=min(z2,y)
// o=max(z1-z2,l2-l1)
// if(o<0):
//      print("0")
// else :
//      print(o)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, rectangles: seq<(int, int)>, m: int, checks: seq<(int, int)>) returns (output: string)
  requires n == |rectangles|
  requires m == |checks|
{
  var l1 := 1000000005;
  var z1 := 0;
  var z2 := 1000000005;
  var l2 := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var x := rectangles[i].0;
    var y := rectangles[i].1;
    if y < l1 { l1 := y; }
    if x > z1 { z1 := x; }
    i := i + 1;
  }
  i := 0;
  while i < m
    invariant 0 <= i <= m
    decreases m - i
  {
    var x := checks[i].0;
    var y := checks[i].1;
    if x > l2 { l2 := x; }
    if y < z2 { z2 := y; }
    i := i + 1;
  }
  var o := z1 - z2;
  if l2 - l1 > o { o := l2 - l1; }
  if o < 0 {
    output := "0";
  } else {
    output := IntToString(o);
  }
}
