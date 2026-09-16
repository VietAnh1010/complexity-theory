// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-10
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     trees := trees[i := (trees[i].0 + trees[i].1, trees[i].1)] performs
//     a full O(n) seq copy each time it executes inside the while i<n-1
//     loop, and that branch can fire on nearly every iteration, giving
//     O(n**2); Python's trees[i] = (...) is an O(1) in-place list write,
//     so the Python stays O(n) as labelled.
//
//   how this label could be wrong, and what to check:
//     The label O(n) assumes the felled-tree update trees[i]=(...) is O(1)
//     as it is in Python. Open the while i<n-1 loop body and confirm the
//     line `trees := trees[i := (trees[i].0 + trees[i].1, trees[i].1)]`;
//     this is a functional seq update (full copy of length n) that can
//     fire on every iteration for a spaced-out tree layout (each tree
//     fells right), making the Dafny loop O(n**2) while Python's in-place
//     trees[i]=(...) list write keeps it O(n).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 25, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 545_C. Woodcutters  (problem 1560, solution 1560_164)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// trees = []
// for i in range(n):
// 	x, h = map(int, input().split())
// 	trees.append((x, h))
// felled = min(2, n)
// for i in range(1,n-1):
// 	left = trees[i][0] - trees[i][1]
// 	right = trees[i][0] + trees[i][1]
// 	if left > trees[i-1][0]:
// 		felled += 1
// 	elif right < trees[i+1][0]:
// 		felled += 1
// 		trees[i] = (trees[i][0] + trees[i][1], trees[i][1])
// print(felled)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<(int, int)>) returns (output: string)
  requires |pairs| == n
{
  var trees := pairs;
  var felled := if n < 2 then n else 2;
  var i := 1;
  while i < n - 1
    invariant 1 <= i
    invariant |trees| == n
    decreases n - 1 - i
  {
    var left := trees[i].0 - trees[i].1;
    var right := trees[i].0 + trees[i].1;
    if left > trees[i-1].0 {
      felled := felled + 1;
    } else if right < trees[i+1].0 {
      felled := felled + 1;
      trees := trees[i := (trees[i].0 + trees[i].1, trees[i].1)];
    }
    i := i + 1;
  }
  output := IntToString(felled);
}
