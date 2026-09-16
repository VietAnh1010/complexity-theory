// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-09
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     `b := b[PyIndex(a_list[i] - 1, |b|) := i+1]` is a seq update inside
//     `while i < n`, costing O(|b|)=O(n) per iteration over n iterations,
//     so the Dafny is O(n**2) even though Python's in-place
//     `B[A[i]-1]=i+1` list assignment is O(1) and keeps the original O(n).
//
//   how this label could be wrong, and what to check:
//     The label also names a second dimension m that does not exist; the
//     signature exposes only one seq argument (a_list) of length n, so
//     first confirm there is no separate m-sized input at all. Then open
//     the while loop and confirm `b := b[PyIndex(...) := i+1]` is a seq
//     update on b (a seq<int>), not an array write; if so it copies all of
//     b each iteration and the method is quadratic.
//
//   structural facts (deterministic, from labelaudit.py):
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
