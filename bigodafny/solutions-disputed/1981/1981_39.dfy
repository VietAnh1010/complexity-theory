// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-14
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The loop `while i < n { ...; b := b[idx := b[idx] + (i+1)]; i := i+1
//     }` performs a seq-update copy of length-n b on every one of n
//     iterations, giving O(n**2), while the Python's list assignment
//     `b[p[i]-1] += i+1` is O(1) in place.
//
//   how this label could be wrong, and what to check:
//     The label assumes b's update is O(1) per element as it is in
//     Python's `b[p[i]-1] += i+1`. Open the while loop and confirm the
//     update is `b := b[idx := b[idx] + (i+1)]`, a seq update; per the
//     cost table a seq update is O(|s|) and it runs inside a loop of n
//     iterations, so the Dafny is quadratic even though the Python mutates
//     a list in place in O(1).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 20, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["JoinInts"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// p03938 AtCoder Grand Contest 007 - Construct Sequences  (problem 1981, solution 1981_39)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// p = list(map(int, input().split()))
// 
// a = [i*40000+1 for i in range(n)]
// b = a[:]
// b.reverse()
// 
// for i in range(n):
//     b[p[i]-1] += i+1
// print(*a)
// print(*b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n >= 0
  requires |a_list| == n
  // Python wraps a negative subscript; 152 occur across the stored tests.
  requires forall k :: 0 <= k < n ==> -n <= a_list[k] - 1 < n
{
  var a := seq(n, i requires 0 <= i < n => i*40000+1);
  var b := seq(n, i requires 0 <= i < n => a[n-1-i]);
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |b| == n
  {
    var idx := PyIndex(a_list[i] - 1, |b|);
    b := b[idx := b[idx] + (i+1)];
    i := i + 1;
  }
  output := JoinInts(a, " ") + "\n" + JoinInts(b, " ") + "\n";
}
