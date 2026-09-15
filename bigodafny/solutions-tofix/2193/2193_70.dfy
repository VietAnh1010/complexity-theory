// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-16
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The outer while loop over distinct is capped at 3 iterations because
//     a_list values are restricted to {1,2,3} per the description, so the
//     inner O(n) scan over a_list runs at most 3 times giving O(n) total,
//     and Sort/SumSeq then operate on a sequence of length at most 3,
//     contributing O(1); the Python's dict-based freq counting over at
//     most 3 keys is likewise O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes real sorting work scales with n, but the
//     description states 'every number is from 1 to 3 inclusively', so
//     distinct (built via `v !in distinct`) never exceeds length 3.
//     Confirm the outer while loop over distinct is bounded by that
//     constant rather than by n; if so the inner O(n) scan runs at most 3
//     times and Sort/SumSeq act on a length-<=3 seq, making the whole
//     method O(n).
//
//   structural facts (deterministic, from labelaudit.py):
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
