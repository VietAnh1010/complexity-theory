// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-batch-05
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     j.sort() in the Python runs on a list built by scanning i from 0
//     upward, so it is already in increasing order and costs O(n) under
//     Timsort's best case, but h.sort() sorts the gap differences
//     -j[f]+j[f+1]-1, which are not pre-ordered, so Python genuinely pays
//     O(n log n) there and the label reflects that real sort. The Dafny
//     drops sorting entirely (facts.sorts is empty) and tracks maxGap
//     directly inside the single while loop over j, giving O(n), so the
//     label is right about the Python and the translation is the defect.
//
//   structural facts (deterministic, from labelaudit.py):
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
