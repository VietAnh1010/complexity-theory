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
//     Solve loops over n test pairs and per test builds the block (kk <=
//     26 steps) and then Repeat(block, reps) + Repeat("a", rem), about nn
//     characters, so the cost is the number of tests times the per-test
//     length, O(n*m), not O(n). The Python alpha[:k]*(n//k) + 'a'*(n%k)
//     builds the same string per test. How the prelude charges
//     Repeat(block, reps) was not checked, hence medium.
//
//   how this label could be wrong, and what to check:
//     The label has a single size, but Solve loops over the test pairs and
//     each test builds a string of length nn. Check Repeat(block, reps) +
//     Repeat("a", rem): they cost the per-test length nn (the loop to kk
//     <= 26 is a block of at most 26 letters), so the cost is tests times
//     string length.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 33, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join", "Repeat"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1092_A. Uniform String  (problem 2254, solution 2254_6)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// """https://codeforces.com/contest/1092/problem/A"""
// alpha = 'abcdefghijklmnopqrstuvwxyz'
// for _ in range(int(input())):
//     n, k = tuple(map(int,input().split()))
//     s = alpha[:k]*(n//k) + 'a'*(n%k)
//     print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
  requires n <= |pairs|
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2
  // k is an alphabet size: at least 1 (it is a divisor) and at most 26
  requires forall k :: 0 <= k < |pairs| ==> 1 <= pairs[k][1] <= 26
  requires forall k :: 0 <= k < |pairs| ==> pairs[k][0] >= 0
{
  var parts: seq<string> := [];
  var t := 0;
  while t < n
    invariant 0 <= t
    decreases n - t
  {
    var nn := pairs[t][0];
    var kk := pairs[t][1];
    var block: string := "";
    var i := 0;
    while i < kk
      invariant 0 <= i
      decreases kk - i
    {
      block := block + [((('a' as int) + i) as char)];
      i := i + 1;
    }
    var reps := nn / kk;
    var rem := nn % kk;
    var s := Repeat(block, reps) + Repeat("a", rem);
    parts := parts + [s];
    t := t + 1;
  }
  output := Join(parts, "\n");
}
