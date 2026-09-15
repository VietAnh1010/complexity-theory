// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(1)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The outer `while i < 55556` loop bound is the literal constant
//     55556, not the parameter n, and n only affects the early-exit test
//     `if |A|==n`; the Python's identical `for i in range(3,55556,2)`
//     shares this fixed cap, so the true cost never grows with n and is
//     O(1), not O(n**2).
//
//   how this label could be wrong, and what to check:
//     The label assumes the sieve's cost scales with n. Check the outer
//     loop bound `i < 55556`: it is a hard-coded literal, not the
//     parameter n, and n only appears in the early-exit `if |A|==n`; since
//     n is constrained 5<=n<=55 by the problem statement and the loop's
//     upper bound never depends on n's value, work done is bounded by a
//     fixed constant.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 37, "data_dependent_loops": 2, "decreases_star":
//     false, "linear_prelude_calls": ["JoinInts"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     true, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// p03362 AtCoder Beginner Contest 096 - Five  Five Everywhere  (problem 1303, solution 1303_8)
// time complexity: O(n**2)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// P, A = [2], [2]
// for i in range(3, 55556, 2):
//     for p in P:
//         if i % p == 0: break
//     else:
//         P.append(i)
//         if i % 5 == 2: A.append(i)
//     if len(A) == n: break
// print(*A)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var P: seq<int> := [2];
  var A: seq<int> := [2];
  var i := 3;
  var doneOuter := false;
  while i < 55556 && !doneOuter
    invariant forall t :: 0 <= t < |P| ==> P[t] >= 2
    decreases 55556 - i
  {
    var isPrime := true;
    var j := 0;
    while j < |P| && isPrime
      invariant 0 <= j <= |P|
      invariant forall t :: 0 <= t < |P| ==> P[t] >= 2
      decreases |P| - j
    {
      if i % P[j] == 0 {
        isPrime := false;
      }
      j := j + 1;
    }
    if isPrime {
      P := P + [i];
      if i % 5 == 2 {
        A := A + [i];
      }
    }
    if |A| == n {
      doneOuter := true;
    }
    i := i + 2;
  }
  output := JoinInts(A, " ") + "\n";
}
