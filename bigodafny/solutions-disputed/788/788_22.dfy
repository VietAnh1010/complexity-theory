// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     For each non-power-of-two element the Dafny loops `while pw <= v`
//     doubling `pw`, O(log a_i) steps, so the cost is O(n log max a_i);
//     the Python's `bin(i)` and `'0'*(len(bin(i))-3)` pay the same bit
//     length.
//
//   how this label could be wrong, and what to check:
//     The label charges each element 1, but both programs pay the
//     element's bit length: the Dafny doubles `pw` until it passes v, and
//     the Python builds `bin(i)` and a string of that many zeros. Check
//     the inner `while pw <= v` loop; it runs log v times per element, a
//     value term.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 56, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 4, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": true, "sorts": [], "uses_map": true,
//     "uses_multiset": false, "uses_set": true}
// --------------------------------------------------------------------

// 1005_C. Summarize to the Power of Two  (problem 788, solution 788_22)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// from collections import defaultdict
// getInputList = lambda : list(input().split())
// getInputIntList = lambda : list(map(int,input().split()))
// 
// n = input()
// arr = getInputIntList()
// 
// myset = defaultdict(lambda:0)
// for i in arr:
// 	myset[i] += 1
// nset = set([])
// for i in arr:
// 	cb = '1'+'0'*(len(bin(i))-3)
// 	if bin(i) == '0b'+cb :
// 		if myset[i] > 1:
// 			nset.add(i)
// 	elif int(cb+'0',2)-i in myset :
// 		#print(i,int(cb+'0',2)-i)
// 		nset.add(i)
// 		nset.add(int(cb+'0',2)-i)
// count = 0
// for i in arr:
// 	if i not in nset:
// 		count += 1
// print(count)		 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires forall k :: 0 <= k < |a_list| ==> 1 <= a_list[k] <= 1000000000
{
  var freq: map<int,int> := map[];
  var j := 0;
  while j < |a_list|
    decreases |a_list| - j
  {
    var v := a_list[j];
    if v in freq {
      freq := freq[v := freq[v] + 1];
    } else {
      freq := freq[v := 1];
    }
    j := j + 1;
  }
  var nset: set<int> := {};
  j := 0;
  while j < |a_list|
    decreases |a_list| - j
  {
    var v := a_list[j];
    var isPow2 := v > 0 && (((v as bv64) & ((v-1) as bv64)) == (0 as bv64));
    if isPow2 {
      if v in freq && freq[v] > 1 {
        nset := nset + {v};
      }
    } else {
      var pw := 1;
      while pw <= v
        invariant pw >= 1
        decreases v - pw
      {
        pw := pw * 2;
      }
      var comp := pw - v;
      if comp in freq {
        nset := nset + {v} + {comp};
      }
    }
    j := j + 1;
  }
  var count := 0;
  j := 0;
  while j < |a_list|
    decreases |a_list| - j
  {
    if a_list[j] !in nset {
      count := count + 1;
    }
    j := j + 1;
  }
  output := IntToString(count);
}
