// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
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
//     The Python sorts the tokens and walks the Counter in sorted order,
//     O(n log n) as labelled; the Dafny keeps a frequency map and returns
//     `n - maxFreq` in a single pass, O(n), replacing the sorted sweep.
//
//   how this label could be wrong, and what to check:
//     The label comes from the Python's `sorted(input().split())` before
//     the Counter. Check that the Dafny never sorts: it computes n minus
//     the maximum frequency in one map pass, a different algorithm in
//     O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 18, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": true,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 651_B. Beautiful Paintings  (problem 1054, solution 1054_212)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// from collections import Counter
// input = sys.stdin.readline
// 
// n = int(input())
// a = dict(Counter(sorted(input().split())))
// 
// ans = 0
// f = 0
// for val in a:
//     ans += min(f, a[val])
//     f += max(a[val] - f, 0)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var counts: map<int, int> := map[];
  var maxFreq := 0;
  var idx := 0;
  while idx < |a_list|
    decreases |a_list| - idx
  {
    var x := a_list[idx];
    var newcount := (if x in counts then counts[x] else 0) + 1;
    counts := counts[x := newcount];
    if newcount > maxFreq { maxFreq := newcount; }
    idx := idx + 1;
  }
  output := IntToString(n - maxFreq);
}

