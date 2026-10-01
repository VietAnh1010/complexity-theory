// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : low
//   auditor        : labelaudit-r3d-06
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny builds `distinct` with a linear seq membership test per
//     element and then runs a full pass over a_list per distinct value, so
//     cost is O(n*d) with no source-level cap on d, whereas the Python
//     counts with a dict in one pass; the label O(nlogn) matches the
//     Python's worst-case sort of counts.
//
//   how this label could be wrong, and what to check:
//     The Dafny scans `distinct` with `v !in distinct` for every element
//     and re-scans a_list once per distinct value, which is O(n*d) with d
//     the number of distinct values, up to n if values are unrestricted.
//     The statement says 1 <= a_i <= 3, so d <= 3 in practice, but the
//     source has no literal bound on d. Decide whether the data cap should
//     make d constant (then the Dafny is O(n) and the label is too loose)
//     or the signature's worst case (O(n**2), against the Python's dict
//     count plus sort of the distinct counts).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 43, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "SumSeq"],
//     "loop_depth": 2, "loops": 3, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     ["Sort"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 52_A. 123-sequence  (problem 2193, solution 2193_70)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// l = list(map(int,input().split()))
// freq = {} 
// for item in l: 
//     if (item in freq): 
//         freq[item] += 1
//     else: 
//         freq[item] = 1
// l = list(sorted(freq.values(),reverse=True))
// l.remove(l[0])
// print(sum(l)) 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| >= 1
{
  var distinct: seq<int> := [];
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant i >= 1 ==> |distinct| >= 1
    decreases |a_list| - i
  {
    var v := a_list[i];
    if v !in distinct { distinct := distinct + [v]; }
    i := i + 1;
  }
  assert |distinct| >= 1;
  var counts: seq<int> := [];
  var j := 0;
  while j < |distinct|
    invariant 0 <= j <= |distinct|
    invariant |counts| == j
    decreases |distinct| - j
  {
    var v := distinct[j];
    var c := 0;
    var k := 0;
    while k < |a_list|
      invariant 0 <= k <= |a_list|
      decreases |a_list| - k
    {
      if a_list[k] == v { c := c + 1; }
      k := k + 1;
    }
    counts := counts + [c];
    j := j + 1;
  }
  assert |counts| >= 1;
  var sortedCounts := Sort(counts, (x: int, y: int) => x > y);
  assert |sortedCounts| >= 1;
  var total := SumSeq(sortedCounts[1..]);
  output := IntToString(total);
}
