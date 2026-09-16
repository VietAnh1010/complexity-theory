// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-08
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     b is declared seq<int>, not array<int>, and `b := b[i := 1]` (plus
//     `b := b[key := 0]`) executes every loop iteration as an O(n)
//     full-seq-copy per the dataset's seq-update rule, giving O(n**2)
//     total that happens to match the label; Python's `b[i]=1` list
//     assignment is O(1), so Python is genuinely O(n) and the agreement
//     with the label is accidental.
//
//   how this label could be wrong, and what to check:
//     not recorded by this batch
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 30, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 889_A. Petya and Catacombs  (problem 1367, solution 1367_88)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// b = [0] * (n + 1)
// res = 1
// b[1] = 1
// for i in range(2, n + 1) :
//     if b[a[i - 1]] == 0 :
//         b[i] = 1
//         res += 1
//     else :
//         b[i] = 1
//         b[a[i - 1]] = 0
// print(res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<int>) returns (output: string)
  requires n >= 0
  requires n == |coordinates|
  requires forall idx :: 1 <= idx < n ==> 0 <= coordinates[idx] <= idx
{
  var b := seq(n + 1, i => 0);
  var res := 1;
  if n >= 1 {
    b := b[1 := 1];
  }
  var i := 2;
  while i <= n
    invariant 2 <= i
    invariant |b| == n + 1
    decreases n - i
  {
    var key := coordinates[i - 1];
    if b[key] == 0 {
      b := b[i := 1];
      res := res + 1;
    } else {
      b := b[i := 1];
      b := b[key := 0];
    }
    i := i + 1;
  }
  output := IntToString(res);
}
