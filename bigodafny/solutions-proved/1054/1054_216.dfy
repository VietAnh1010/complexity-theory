// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
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
//     The Python's rounds scan and remove from lists, quadratic as
//     labelled; the Dafny counts frequencies in the map `counts` in one
//     pass and outputs `n - maxFreq`, O(n), so the algorithm was replaced.
//
//   how this label could be wrong, and what to check:
//     The Python repeatedly builds a distinct list with `x not in
//     self.m_Y` and deletes it with `self.m_X.remove(x)`, both list scans,
//     O(n**2) when values are distinct. Check that the Dafny instead makes
//     one map-counting pass; it reaches the same answer in O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 18, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": true,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 651_B. Beautiful Paintings  (problem 1054, solution 1054_216)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # -*- codeing:utf-8 -*-
// 
// class A(object):
// 	def __init__(self):
// 		self.AC()
// 
// 	def GetData(self):
// 		self.m_N = int(input())
// 		self.m_X = [int(x) for x in input().split()]
// 
// 	def AC(self):
// 		self.GetData()
// 		ans = 0
// 		while self.m_X:
// 			self.m_Y = []
// 			for x in self.m_X:
// 				if x not in self.m_Y:
// 					self.m_Y.append(x)
// 			ans += (len(self.m_Y)-1)
// 			for x in self.m_Y:
// 				self.m_X.remove(x)
// 		print(ans)
// 
// A()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 10 * |a_list| + |output| + 3
{
  steps := 1;
  var counts: map<int, int> := map[];
  var maxFreq := 0;
  var idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant steps <= 10 * idx + 1
    decreases |a_list| - idx
  {
    var x := a_list[idx];
    var newcount := (if x in counts then counts[x] else 0) + 1;
    counts := counts[x := newcount];
    if newcount > maxFreq { maxFreq := newcount; }
    idx := idx + 1;
    steps := steps + 10;
  }
  IntToStringDigits(n - maxFreq);
  output := IntToString(n - maxFreq);
  steps := steps + 1 + Digits(n - maxFreq);
}
