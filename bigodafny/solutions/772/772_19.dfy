// 339_D. Xenia and Bit Operations  (problem 772, solution 772_19)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// reader = (line.rstrip() for line in sys.stdin)
// input = reader.__next__
// 
// class SegmentTree() :
// 	def __init__(self, size):
// 		N = 1
// 		while N < size:
// 			N <<= 1
// 			self.N = N
// 			self.tree = [0] * (2 * N)
// 
// 	def update(self, index, value) :
// 		index += self.N
// 		self.tree[index] = value
// 		flag = False
// 		while index > 1 :
// 			if flag :
// 				self.tree[index >> 1] = self.tree[index] ^ self.tree[index ^ 1]
// 			else :
// 				self.tree[index >> 1] = self.tree[index] | self.tree[index ^ 1]
// 			flag = not flag
// 			index >>= 1
// 
// n, m = map(int, input().split())
// arr = list(map(int, input().split()))
// st = SegmentTree(1 << n)
// for index, value in enumerate(arr) :
// 	st.update(index, value)
// for _ in range(m) :
// 	index, value = map(int, input().split())
// 	st.update(index - 1, value)
// 	print(st.tree[1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, weights: seq<int>, edges: seq<seq<int>>) returns (output: string)
{
  var size := 1;
  var t := 0;
  while t < n
    decreases n - t
  {
    size := size * 2;
    t := t + 1;
  }
  var tree := new int[2*size];
  var idx := 0;
  while idx < size
    decreases size - idx
  {
    var val := if idx < |weights| then weights[idx] else 0;
    var pos := idx + size;
    tree[pos] := val;
    var p := pos;
    var orLevel := true;
    while p > 1
      decreases p
    {
      p := p / 2;
      var l := tree[2*p]; var r := tree[2*p+1];
      if orLevel {
        tree[p] := ((l as bv64) | (r as bv64)) as int;
      } else {
        tree[p] := ((l as bv64) ^ (r as bv64)) as int;
      }
      orLevel := !orLevel;
    }
    idx := idx + 1;
  }
  var lines: seq<string> := [];
  var qi := 0;
  while qi < |edges|
    decreases |edges| - qi
  {
    var qidx := edges[qi][0] - 1;
    var qval := edges[qi][1];
    var pos := qidx + size;
    tree[pos] := qval;
    var p := pos;
    var orLevel := true;
    while p > 1
      decreases p
    {
      p := p / 2;
      var l := tree[2*p]; var r := tree[2*p+1];
      if orLevel {
        tree[p] := ((l as bv64) | (r as bv64)) as int;
      } else {
        tree[p] := ((l as bv64) ^ (r as bv64)) as int;
      }
      orLevel := !orLevel;
    }
    lines := lines + [IntToString(tree[1])];
    qi := qi + 1;
  }
  output := Join(lines, "\n");
}
