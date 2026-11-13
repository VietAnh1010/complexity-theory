// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
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
//     The Python tests `o not in c` against a list and calls `a.count(i)`
//     for each distinct value, O(n**2) as labelled; the Dafny instead
//     sorts with `SortInts(numbers)` and counts runs, O(n log n),
//     replacing the algorithm.
//
//   how this label could be wrong, and what to check:
//     The Python is quadratic: `o not in c` scans a list and `a.count(i)`
//     scans a once per distinct value. Check that the Dafny does neither:
//     it sorts with `SortInts` and counts runs, which is O(n log n), a
//     class faster than the labelled program.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 30, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": ["SortInts"], "uses_map":
//     false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1032_A. Kitchen Utensils  (problem 138, solution 138_449)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import ceil
// n, m = [int(s) for s in input().split()]
// a = [int(s) for s in input().split()]
// # c, d = np.unique(a), np.unique(a, return_counts=True)[1]
// c = []
// cnt = 0
// for o in a:
//     if o not in c:
//         c.append(o)
// d = []
// for i in c:
// 	d.append(a.count(i))
// dishes, set = ceil(max(d) / m), len(c) #���������� ����, ������� � ����� ����
// eta = dishes * set * m
// print(eta - n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, numbers: seq<int>) returns (output: string)
  requires k >= 1
{
  var sorted := SortInts(numbers);
  var m := |sorted|;
  var maxCount := 0;
  var distinct := 0;
  var i := 0;
  while i < m
    decreases m - i
  {
    var j := i;
    while j < m && sorted[j] == sorted[i]
      decreases m - j
    {
      j := j + 1;
    }
    var cnt := j - i;
    if cnt > maxCount {
      maxCount := cnt;
    }
    distinct := distinct + 1;
    i := j;
  }
  var dishes := if maxCount % k == 0 then maxCount / k else maxCount / k + 1;
  var eta := dishes * distinct * k;
  output := IntToString(eta - n);
}
