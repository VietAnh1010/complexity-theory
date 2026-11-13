// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python evaluates `j + 1 in set(x)` for each of n indices,
//     rebuilding the set every time, O(n**2); the Dafny marks
//     `present[(v-1) := true]` in one pass and counts in another, O(n).
//
//   how this label could be wrong, and what to check:
//     The Python rebuilds `set(x)` inside the loop over j, an O(n)
//     construction n times, so it is O(n**2) as labelled. Check that the
//     Dafny marks presence once in the seq `present` and never rebuilds;
//     it is O(n), a class faster.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 28, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 137_B. Permutation  (problem 1413, solution 1413_222)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// x = list(map(int, input().split()))
// a, list_of_set = n * [0], n * [0]
// ans = 0
// for i in range(1, n + 1):
//     a[i - 1] = i
// for j in range(n):
//     if j + 1 in set(x):
//         list_of_set[j] = j + 1
// for k in range(n):
//     if list_of_set[k] != a[k]:
//         ans += 1
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, values: seq<int>) returns (output: string)
  requires n >= 1
{
  var present := seq(n, i => false);
  var idx := 0;
  while idx < |values|
    invariant |present| == n
    decreases |values| - idx
  {
    var v := values[idx];
    if 1 <= v <= n {
      present := present[(v-1) := true];
    }
    idx := idx + 1;
  }
  var cnt := 0;
  var j := 0;
  while j < n
    invariant 0 <= j && |present| == n
    decreases n - j
  {
    if !present[j] { cnt := cnt + 1; }
    j := j + 1;
  }
  output := IntToString(cnt);
}
