// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-s02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The only loop runs i from 0 to n writing b[PyIndex(a_list[i] - 1,
//     |b|)] and JoinInts(b) is linear in n; a_list holds exactly n values,
//     so there is one size and the cost is O(n). The Python's `for i in
//     range(N)` over A of length N is O(N) too, so the second variable m
//     in O(n+m) names a size that does not exist.
//
//   how this label could be wrong, and what to check:
//     The label O(n+m) implies two independent sizes, but the signature is
//     (n, a_list) with n <= |a_list| and the statement gives A the same
//     length N. Check the problem input: N followed by N values means
//     there is one size; if A could be longer than N and the Python
//     scanned all of it, then n+m would be right.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 19, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["JoinInts"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// p02899 AtCoder Beginner Contest 142 - Go to School  (problem 1421, solution 1421_53)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N = int(input())
// A = [int(i) for i in input().split()]
// B=[0]*N
// for i in range(N):
//   B[A[i]-1]=i+1
// print(*B)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n >= 0
  requires n <= |a_list|
  // Python's own domain for this subscript: it wraps for a negative index and
  // raises outside [-n, n). 152 negative indices occur across the stored tests.
  requires forall k :: 0 <= k < n ==> -n <= a_list[k] - 1 < n
{
  var b := seq(n, i => 0);
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |b| == n
    decreases n - i
  {
    b := b[PyIndex(a_list[i] - 1, |b|) := i+1];
    i := i + 1;
  }
  output := JoinInts(b, " ");
}
