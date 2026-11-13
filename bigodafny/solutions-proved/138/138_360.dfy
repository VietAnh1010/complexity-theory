// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(nlogn)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny calls `SortInts(numbers)` and then counts runs in the
//     sorted sequence, O(n log n); the Python counts occurrences with the
//     dict `maps` in a single pass, O(n), so the translation swapped the
//     algorithm for a slower one.
//
//   how this label could be wrong, and what to check:
//     The Python counts with a dict in one pass, which is O(n) as
//     labelled. Check the Dafny's first line, `SortInts(numbers)`: the
//     sort replaces the dict and costs O(n log n). A map-based count would
//     restore O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 32, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": ["SortInts"], "uses_map":
//     false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1032_A. Kitchen Utensils  (problem 138, solution 138_360)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int, input().split())
// arr = list(map(int, input().split()))
// 
// curMax = 0
// maps = {}
// for a in arr:
//     if a not in maps:
//         maps[a] = 1
//     else:
//         maps[a] += 1
//     curMax = max(curMax, maps[a])
// 
// if curMax % k != 0:
//     curMax = curMax - (curMax % k) + k
// 
// print (curMax * len(maps) - len(arr))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires k >= 1
  ensures steps <= 2 * NLogN(|numbers|) + 20 * |numbers| + |output| + 20
{
  steps := 1;
  var sorted := SortInts(numbers);
  steps := steps + SortCost(|numbers|);
  SortCostWithin(|numbers|, |numbers|);
  var m := |sorted|;
  var curMax := 0;
  var distinct := 0;
  var i := 0;
  ghost var base := steps;
  while i < m
    invariant 0 <= i <= m
    invariant steps <= base + 20 * i
    decreases m - i
  {
    var j := i;
    ghost var s0 := steps;
    while j < m && sorted[j] == sorted[i]
      invariant i <= j <= m
      invariant steps <= s0 + 5 * (j - i)
      decreases m - j
    {
      j := j + 1;
      steps := steps + 5;
    }
    var cnt := j - i;
    if cnt > curMax {
      curMax := cnt;
    }
    distinct := distinct + 1;
    i := j;
    steps := steps + 15;
  }
  if curMax % k != 0 {
    curMax := curMax - (curMax % k) + k;
  }
  var result := curMax * distinct - |numbers|;
  output := IntToString(result);
  IntToStringDigits(result);
  steps := steps + 10 + Digits(result);
}
