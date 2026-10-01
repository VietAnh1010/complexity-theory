// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-r3d-02
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python sorts j and h and pops the maximum gap, which is O(n log
//     n), while the Dafny never sorts: it scans s once to build j and once
//     more keeping a running maxGap, all O(1) amortised steps, so it is
//     O(n). The algorithm was replaced by a faster one, so the label is
//     right about the Python and the Dafny lands a class lower.
//
//   how this label could be wrong, and what to check:
//     The label comes from the Python's `j.sort()` and `h.sort()`. Check
//     that the Dafny has no Sort/SortInts call and only does two linear
//     scans (the `j := j + [i]` loop and the max-gap loop). If the Dafny's
//     maxGap scan is accepted as the intended algorithm, the translation
//     replaced the sort+pop with a running max.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 29, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 2,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 299_B. Ksusha the Squirrel  (problem 641, solution 641_25)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = input().split()
// n = int(n)
// k = int(k)
// a = list(input())
// i = 0
// j = []
// while i < n:
//     if a[i] == ".":
//         j.append(i)
//     i += 1
// h = []
// j.sort()
// f = 0
// while f < len(j) - 1:
//     h.append(-j[f] + j[f+1] - 1)
//     f += 1
// h.sort()
// if h.pop() >= k:
//     print("NO")
// else:
//     print("YES")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, s: string) returns (output: string)
{
  var j: seq<int> := [];
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if s[i] == '.' {
      j := j + [i];
    }
    i := i + 1;
  }
  var maxGap := -1;
  var f := 0;
  while f + 1 < |j|
    decreases |j| - f
  {
    var gap := j[f+1] - j[f] - 1;
    if gap > maxGap { maxGap := gap; }
    f := f + 1;
  }
  if maxGap >= m {
    output := "NO";
  } else {
    output := "YES";
  }
}
