// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-u01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over the t queries and for each runs an inner loop to
//     the value nn building the string with s + [c] (O(1) amortised), so
//     O(t * n_i), two different sizes multiplied, and Join is linear in
//     output; the Python's inner range(0, n) loop is the same, so O(n**2)
//     does not name the sizes.
//
//   how this label could be wrong, and what to check:
//     The label O(n**2) squares one size, but the two quantities are the
//     query count t and the per-query length n_i. Find the outer `while t
//     < n` over queries and the inner `while i < nn` where nn =
//     pairs[t][0]: nested loops to two input quantities. Per the naming
//     rule that is O(n*m).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 32, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 2, "loops":
//     2, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1092_A. Uniform String  (problem 2254, solution 2254_143)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for i in range(int(input())):
//     n,k=map(int,input().split())
//     s=""
//     x=0
//     for i in range(0,n):
//         s=s+chr(x+97)
//         x+=1
//         x=x%k
//     print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
  requires n <= |pairs|
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2
  // k is an alphabet size: at least 1 (it is a divisor) and at most 26
  requires forall k :: 0 <= k < |pairs| ==> 1 <= pairs[k][1] <= 26
{
  var parts: seq<string> := [];
  var t := 0;
  while t < n
    invariant 0 <= t
    decreases n - t
  {
    var nn := pairs[t][0];
    var kk := pairs[t][1];
    var s: string := "";
    var x := 0;
    var i := 0;
    while i < nn
      invariant 0 <= x < kk
      decreases nn - i
    {
      s := s + [((x + 97) as char)];
      x := x + 1;
      x := x % kk;
      i := i + 1;
    }
    parts := parts + [s];
    t := t + 1;
  }
  output := Join(parts, "\n");
}
