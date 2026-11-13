// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny counts into `freq` in one pass over n elements and sorts
//     `vals`, which holds at most three counts because each a_i is 1, 2 or
//     3, so the cost is O(n); the Python's `sorted(freq.values())` sorts
//     the same three counts.
//
//   how this label could be wrong, and what to check:
//     The label's log factor comes from `sorted(freq.values())`, but every
//     element is 1, 2 or 3, so `freq` has at most three keys and the sort
//     is constant. Check the problem statement's value set; with three
//     possible values the class is the O(n) counting pass.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 38, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "SumSeq"],
//     "loop_depth": 1, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts":
//     ["Sort"], "uses_map": true, "uses_multiset": false, "uses_set":
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
  // freq, with its keys in insertion order (Python dict order)
  var freq: map<int, int> := map[];
  var order: seq<int> := [];
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant i >= 1 ==> |order| >= 1
    invariant forall k :: 0 <= k < |order| ==> order[k] in freq
    invariant forall x :: x in freq ==> x in order
    decreases |a_list| - i
  {
    var item := a_list[i];
    if item in freq {
      freq := freq[item := freq[item] + 1];
    } else {
      freq := freq[item := 1];
      order := order + [item];
    }
    i := i + 1;
  }
  // freq.values()
  var vals: seq<int> := [];
  var j := 0;
  while j < |order|
    invariant 0 <= j <= |order|
    invariant |vals| == j
    decreases |order| - j
  {
    vals := vals + [freq[order[j]]];
    j := j + 1;
  }
  var l := Sort(vals, (x: int, y: int) => x > y);
  // l.remove(l[0]) drops index 0
  l := l[1..];
  output := IntToString(SumSeq(l));
}
