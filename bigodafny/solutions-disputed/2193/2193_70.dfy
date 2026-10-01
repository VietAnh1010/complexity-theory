// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : low
//   auditor        : labelaudit-r4-u01
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     Solve scans the seq `distinct` for each element and then rescans
//     a_list once per distinct value, O(n*d) with d the distinct count,
//     which is O(n**2) when values are unrestricted, whereas the Python's
//     dict is O(n) plus sorting d counts; I lean translation, as the Dafny
//     replaced a dict by a linear seq search.
//
//   how this label could be wrong, and what to check:
//     The label O(nlogn) matches the Python, which counts with a dict and
//     sorts the counts. Check the Dafny `v !in distinct` over a seq and
//     the `while j < |distinct|` pass that rescans a_list per distinct
//     value: with no requires bounding the values, distinct can grow to n
//     and the cost is O(n**2). If you instead honour the statement's 1 <=
//     a_i <= 3 cap, distinct has at most 3 entries, the Dafny is O(n) and
//     the label is simply too loose (cause label).
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
