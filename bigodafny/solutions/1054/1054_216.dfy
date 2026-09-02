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

