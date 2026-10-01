// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over the test rows and per test calls IntSqrtFloor (log
//     k steps, at most about log n) and three RepStr calls whose counts
//     sum to nn, so each test is O(nn) and the total is tests times string
//     length, O(n*m), not O(n). The Python builds A = ['a' for i in
//     range(n)] and the string R per test, also O(n) per test. The sqrt
//     search is dominated by the string building.
//
//   how this label could be wrong, and what to check:
//     The label has one size, but Solve loops over the tests and per test
//     builds strings of length nn with RepStr. Check RepStr("a", nn - x -
//     1) and the other two calls: each recurses on a per-test count, and
//     the loop `while t < |pairs_list|` is outside them.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 49, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 1, "loops":
//     2, "recursive_helpers": 2, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1328_B. K-th Beautiful String  (problem 2819, solution 2819_926)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # Anuneet Anand 
// import math
// T = int(input())
// 
// while T:
// 	n,k = map(int,input().split())
// 	x = int(((1) + math.sqrt(1 + (8 * (k-1)))) / 2)
// 	d = int(math.floor((-1 + math.sqrt(1+ 8 * k - 8)) / 2)) 
// 	b = (d * (d + 1)) / 2 + 1 
// 	y = int(k - b)
// 	A = ['a' for i in range(n)]
// 	A[n-x-1]='b'
// 	A[n-y-1]='b'
// 	R = "a"*(n-x-1)+"b"+"a"*(x-y-1)+"b" + y*"a"
// 	print(R)
// 	T = T-1
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method IntSqrtFloor(v: int) returns (r: int)
  requires v >= 0
{
  var lo := 0;
  var hi := v + 1;
  while lo < hi
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if mid * mid <= v {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  r := lo - 1;
}

function RepStr(s: string, n: int): string
  decreases if n > 0 then n else 0
{
  if n <= 0 then "" else s + RepStr(s, n - 1)
}

method Solve(n: int, pairs_list: seq<seq<int>>) returns (output: string)
{
  var results: seq<string> := [];
  var t := 0;
  while t < |pairs_list|
    invariant 0 <= t <= |pairs_list|
  {
    var row := pairs_list[t];
    if |row| >= 2 {
      var nn := row[0];
      var k := row[1];
      var val := 8 * k - 7;
      if val < 0 { val := 0; }
      var s := IntSqrtFloor(val);
      var x := FloorDiv(1 + s, 2);
      var d := FloorDiv(s - 1, 2);
      var b := FloorDiv(d * (d + 1), 2) + 1;
      var y := k - b;
      var r := RepStr("a", nn - x - 1) + "b" + RepStr("a", x - y - 1) + "b" + RepStr("a", y);
      results := results + [r];
    }
    t := t + 1;
  }
  output := Join(results, "\n");
}
