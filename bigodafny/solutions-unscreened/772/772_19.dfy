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

function Pow2_772(k: int): int
{
  if k <= 0 then 1 else 2 * Pow2_772(k - 1)
}

method Solve(n: int, m: int, weights: seq<int>, edges: seq<seq<int>>) returns (output: string)
  requires n >= 1
  requires forall k :: 0 <= k < |weights| ==> 0 <= weights[k] < 0x4000_0000
  requires forall k :: 0 <= k < |edges| ==> |edges[k]| == 2 && 1 <= edges[k][0] <= Pow2_772(n) && 0 <= edges[k][1] < 0x4000_0000
{
  var size := 1;
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    invariant size == Pow2_772(t)
    decreases n - t
  {
    size := size * 2;
    t := t + 1;
  }
  assert size >= 1 by { Pow2Pos_772(n); }
  var tree := new int[2*size](_ => 0);
  var idx := 0;
  while idx < size
    invariant tree.Length == 2 * size
    invariant forall k :: 0 <= k < tree.Length ==> 0 <= tree[k] < 0x1_0000_0000_0000_0000
    decreases size - idx
  {
    var val := if idx < |weights| then weights[idx] else 0;
    var pos := idx + size;
    tree[pos] := val;
    var p := pos;
    var orLevel := true;
    while p > 1
      invariant 1 <= p < 2 * size
      invariant forall k :: 0 <= k < tree.Length ==> 0 <= tree[k] < 0x1_0000_0000_0000_0000
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
    invariant tree.Length == 2 * size
    invariant forall k :: 0 <= k < tree.Length ==> 0 <= tree[k] < 0x1_0000_0000_0000_0000
    decreases |edges| - qi
  {
    var qidx := edges[qi][0] - 1;
    var qval := edges[qi][1];
    var pos := qidx + size;
    tree[pos] := qval;
    var p := pos;
    var orLevel := true;
    while p > 1
      invariant 1 <= p < 2 * size
      invariant forall k :: 0 <= k < tree.Length ==> 0 <= tree[k] < 0x1_0000_0000_0000_0000
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

lemma Pow2Pos_772(k: int)
  ensures Pow2_772(k) >= 1
  decreases if k <= 0 then 0 else k
{
  if k > 0 { Pow2Pos_772(k - 1); }
}
