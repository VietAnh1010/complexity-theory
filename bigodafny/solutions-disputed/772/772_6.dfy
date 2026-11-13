// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : both
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     The Dafny initialises each of the 2**n leaves with an update that
//     climbs n levels, O(N log N), then m updates of log N; the Python's
//     `build_seg_tree` is one O(N) bottom-up pass followed by the same m
//     log N updates.
//
//   how this label could be wrong, and what to check:
//     Two faults. The Python builds the tree bottom-up in O(N) but then
//     runs m updates of log N each, so O(n) omits the queries. The Dafny
//     builds by calling the climbing update once per leaf, O(N log N).
//     Check the Dafny's first `while idx < size` loop against the Python's
//     single `for i in range(n-1, 0, -1)` build.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 88, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 2, "loops": 5, "recursive_helpers": 2,
//     "seq_append_read_in_same_loop": false, "seq_args": 2,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 339_D. Xenia and Bit Operations  (problem 772, solution 772_6)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #Xenia and Bit Operations
// #from operator import or_, xor
// import sys
// 
// def ispow2(n): #doesn't work for n = 0.
//     neg = n & (n-1)
//     if neg == 0:
//         return True
//     else:
//         return False
// 
// def build_seg_tree(n, a): #n is length of a. Tree will have high-level nodes from 1 to n-1, and array will start at n to 2n-1, for a total length of 2n.
//     #Position 0 will be 0 and unused.
//     tree = [0] * (n) #upper nodes of tree.
//     tree.extend(a) #leaves of tree.
//     #Build upper nodes. 
//     ###Unique based on specific problem, but always tree[i] based on tree[2*i] and tree[(2*i)+1]
//     or_level = True
//     for i in range(n-1, 0, -1):
//         if or_level:
//             tree[i] = tree[2*i] | tree[(2*i)+1]
//         else:
//             tree[i] = tree[2*i] ^ tree[(2*i)+1]
//         if ispow2(i):
//             or_level = not or_level
//     #print('initial tree=', tree)
//     return tree
// 
// def modify_seg_tree(tree, pos, val):
//     n = len(tree) // 2
//     pos += n #Converts to n-based array in tree.
//     tree[pos] = val #initial change based on query from CF.
//     or_level = True
//     while pos > 1:
//         pos = pos // 2
//         if or_level:
//             tree[pos] = tree[2*pos] | tree[(2*pos)+1]
//         else:
//             tree[pos] = tree[2*pos] ^ tree[(2*pos)+1]
//         
//         or_level = not or_level
//         
//     #print(tree)
// 
//     return
// 
// def query_seg_tree(tree, pos):
//     #This problem pos = 1
//     return tree[pos]
// 
// def answer(n, m, a, p, b):
//     #answer gets called once.
//     #Build segment tree
//     tree = build_seg_tree(2**n, a) #This specific problem gave length as power of two.
//     for i in range(m): # # of queries
//         modify_seg_tree(tree, p[i]-1, b[i]) #i-1 because CF uses 1-based arrays and we want 0-based arrays.
//         print(query_seg_tree(tree, 1)) # usually lpos & rpos, but here only 1 because the modification affects the top.
//         #print(tree[1])
//     return 
// 
// def main():
//     n, m = [int(i) for i in input().split()]
//     a = [int(i) for i in input().split()]
//     p = [0] * m
//     b = [0] * m
//     for j in range(m):
//         #p[j], b[j] = [int(i) for i in input().split()]
//         p[j], b[j] = [int(i) for i in sys.stdin.readline().split()]
//     answer(n, m, a, p, b)
// 
//     return
// 
// main()
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
