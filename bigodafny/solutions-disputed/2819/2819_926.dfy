// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : both
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     The Dafny's `RepStr` prepends one character per recursion level and
//     each `s + RepStr(...)` concat costs the tail's length, so each test
//     costs O(n_i**2 + log k); the Python's `"a"*m` repetition and list
//     `A` are O(n_i) per test.
//
//   how this label could be wrong, and what to check:
//     Two faults. Each test builds a list `A` of length n_i and takes two
//     square roots, so the Python is O(T*(n + log k)), a per-test size the
//     O(n) label omits. The Dafny's `RepStr(s, n)` builds a run of 'a' by
//     `s + RepStr(s, n - 1)`, a concat charged the tail's length at every
//     level, O(n**2) per run. Check `RepStr` against the Python's
//     `"a"*(n-x-1)`.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 34, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 1, "loops":
//     1, "recursive_helpers": 1, "seq_append_read_in_same_loop": false,
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

function RepStr(s: string, n: int): string
  decreases if n > 0 then n else 0
{
  if n <= 0 then "" else s + RepStr(s, n - 1)
}

method Solve(n: int, pairs_list: seq<seq<int>>) returns (output: string)
  requires forall t :: 0 <= t < |pairs_list| && |pairs_list[t]| >= 2 ==>
    pairs_list[t][0] >= 3 && 1 <= pairs_list[t][1] &&
    2 * pairs_list[t][1] <= pairs_list[t][0] * (pairs_list[t][0] - 1)
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
      var x := FloorDiv(1 + ISqrt(val), 2);
      var d := FloorDiv(ISqrt(val) - 1, 2);
      var b := FloorDiv(d * (d + 1), 2) + 1;
      var y := k - b;
      var r := RepStr("a", nn - x - 1) + "b" + RepStr("a", x - y - 1) + "b" + RepStr("a", y);
      results := results + [r];
    }
    t := t + 1;
  }
  output := Join(results, "\n");
}
