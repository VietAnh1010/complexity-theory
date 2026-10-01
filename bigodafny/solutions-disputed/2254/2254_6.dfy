// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-13
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The outer loop runs t = n times and each iteration pays an inner
//     loop to the per-query value kk plus Repeat building nn characters,
//     so the cost is O(t + sum of per-query n_i + k_i), a value term the
//     label's n (the query count) does not account for; the Python slicing
//     and multiplication pays the same.
//
//   how this label could be wrong, and what to check:
//     The label claims linear in one n, but the cost has per-query value
//     terms. Open the Dafny and find the inner `while i < kk` loop and the
//     Repeat(block, reps) calls inside `while t < n`: each is bounded by
//     the per-query values pairs[t][1] and pairs[t][0], not by the query
//     count n. If n is read as the total output length the label stands;
//     as the signature's t it does not.
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
